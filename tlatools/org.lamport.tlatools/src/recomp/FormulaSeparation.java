package recomp;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.MultiTraceCex;
import cmu.isr.ts.lts.SafetyUtils;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.TLC;
import tlc2.Utils;
import tlc2.tool.impl.FastTool;

public class FormulaSeparation {
	private static final String TLC_JAR_PATH = System.getProperty("user.home") + "/bin/tla2tools.jar";
	private static final long NEG_TRACE_TIMEOUT = System.getenv("FSYNTH_NEG_TRACE_TIMEOUT") != null ?
			Long.parseLong(System.getenv("FSYNTH_NEG_TRACE_TIMEOUT")) : 5L;
	
	private final String tlaComp;
	private final String cfgComp;
	private final String tlaRest;
	private final String cfgRest;
	private final String tlaSys;
	private final String cfgSys;
	private final boolean useIntermediateProp;
	private final Formula intermediateProp;
	private final TLC tlcComp;
	private final TLC tlcRest;
	private final TLC tlcSys;
	private final Set<String> globalActions;
	private final Set<String> internalActions;
	private final Map<String, Set<String>> sortElementsMap;
	private final Map<String, Set<String>> rawSortElementsMap;
	private final Map<String, Map<String, Set<String>>> setSortElementsMap;
	private final Map<String, List<String>> actionParamTypes;
	private final int maxActParamLen;
	private final int maxNumVarsPerType;
	private final Set<String> qvars;
	private final Set<Set<String>> legalEnvVarCombos;
	private final Set<Map<String,String>> allPermutations;
	private final Random seed;
	
	private Map<Utils.Pair<AlloyTrace, String>, Boolean> traceInSpecCache;
	
	public FormulaSeparation(final String tlaComp, final String cfgComp, final String tlaRest, final String cfgRest,
			final String tlaSys, final String cfgSys, final String propFile, long rseed) {
		this.tlaComp = tlaComp;
		this.cfgComp = cfgComp;
		this.tlaRest = tlaRest;
		this.cfgRest = cfgRest;
		this.tlaSys = tlaSys;
		this.cfgSys = cfgSys;
		
		tlcComp = new TLC();
    	tlcComp.initialize(tlaComp, cfgComp);
		tlcRest = new TLC();
    	tlcRest.initialize(tlaRest, cfgRest);
		tlcSys = new TLC();
    	tlcSys.initialize(tlaSys, cfgSys);
		
    	// the property file that's used for "intermediate" (i.e. fluent) properties
		this.useIntermediateProp = !propFile.equals("none");
		this.intermediateProp = this.useIntermediateProp ? new Formula( String.join("",Utils.fileContents(propFile)) ) : null;
		
		// the actions that are in the shared alphabet between comp and rest.
    	globalActions = Utils.intersection(tlcComp.actionsInSpec(), tlcRest.actionsInSpec());
    	
    	// the actions that internal to "component". it is fine to include formulas over actions that
		// are internal to "rest" so we don't mark those as "internal".
    	internalActions = Utils.setMinus(tlcComp.actionsInSpec(), tlcRest.actionsInSpec());
    	
    	// obtain a map of: sort -> Set(elements/atoms in the sort)
    	sortElementsMap = createSortElementsMap(tlcSys, true); // sanitized tokens
    	rawSortElementsMap = createSortElementsMap(tlcSys, false); // unsanitiszed tokens
    	
    	// obtain a map of: sort -> Set(elements/atoms in the sort) -> Set(elements/atoms in each set in the sort)
    	setSortElementsMap = createSetSortElementsMap(tlcSys);
    	
    	// calculate all permutations of the sort elements
    	allPermutations = calcAllPermutations();
		
		// obtain a map of: action -> List(param type)
    	FastTool ft = (FastTool) tlcSys.tool;
		actionParamTypes = TLC.getTransitionRelationNode(ft, tlcSys, "Next").actionParamTypes(tlcSys.actionsInSpec());
		maxActParamLen = actionParamTypes.values()
				.stream()
				.mapToInt(l -> l.size())
				.max()
				.getAsInt();

		maxNumVarsPerType = 3; // TODO make this a param
		final int maxNumVars = 3; // TODO make the number of vars a param
		final int numTypes = sortElementsMap.keySet().size();
		final int numVars = Math.min(maxNumVars, maxNumVarsPerType*numTypes);
		final String varNameBase = "var";
		qvars = IntStream.range(0, numVars)
				.mapToObj(i -> varNameBase + i)
				.collect(Collectors.toSet());
		
		legalEnvVarCombos = IntStream.range(0, numVars)
				.mapToObj(i ->
					IntStream.range(0, i+1)
						.mapToObj(j -> varNameBase + j)
						.collect(Collectors.toSet()))
				.collect(Collectors.toSet());
		
		seed = new Random(rseed);
		
		traceInSpecCache = new HashMap<>();
	}
	
	public String synthesizeSepInvariant() {
    	// config for producing positive traces
    	final String strCfgConstants = String.join("\n", tlcSys.tool.getModelConfig().getRawConstants());
    	final String cfgPosTraces = "pos_traces.cfg";
    	Utils.writeFile(cfgPosTraces, "SPECIFICATION Spec\nINVARIANT CandSep\n" + strCfgConstants);
    	
    	// config for producing negative traces
    	final String cfgNegTraces = "neg_traces.cfg";
    	final String negTracesSafety = this.useIntermediateProp ? "\nINVARIANT Safety" : "";
    	Utils.writeFile(cfgNegTraces, String.join("\n", Utils.fileContents(cfgComp)) + negTracesSafety);
    	
    	//final List<String> rawComponents = Decomposition.decompAll(tla, cfg);
    	//final List<String> components = Composition.symbolicCompose(tla, cfg, "CUSTOM", "recomp_map.csv", rawComponents);
    	
		// split inference into several jobs, where each job assigns possible types to variables
		// note: the variable orderings matter because of the legal environments we chose (see legalEnvVarCombos)
		// so we need to consider the order of vars, not just how many of each type
		final Set<String> allTypes = this.actionParamTypes.entrySet()
				.stream()
				.filter(e -> this.globalActions.contains(e.getKey())) // only consider types from global actions
				.map(e -> e.getValue())
				.map(l -> l.stream().collect(Collectors.toSet()))
				.reduce((Set<String>)new HashSet<String>(),
						(acc,s) -> Utils.union(acc, s),
						(s1,s2) -> Utils.union(s1, s2));
		final Set<Map<String,String>> allEnvVarTypes = createAllEnvVarTypes(allTypes);
		Utils.assertTrue(!allEnvVarTypes.isEmpty(), "internal error: envVarTypes is empty!");
    	
		// a minimal length "default" init pos trace we can use, in the case that the dynamically generated one
		// (below) has 0 length (i.e. is not a real trace).
    	final AlloyTrace defaultInitPosTrace = createInitPosTrace();
    	
    	List<Formula> invariants = new ArrayList<>();
    	boolean formulaSeparates = false;
    	
    	int round = 1;
    	while (!formulaSeparates) {
    		System.out.println("Round " + round);
    		System.out.println("-------");
    		PerfTimer timer = new PerfTimer();
    		
    		// the env var types we consider for this round. it always starts as the full set, but then we eliminate
    		// any env var type that returns UNSAT. note that envVarTypes gets modified (as an out-param) in the
    		// synthesizeFormula() method.
    		Set<Map<String,String>> envVarTypes = new HashSet<>(allEnvVarTypes);
    		
    		// generate a negative trace for this round; we will generate a formula (assumption) that eliminates
    		// the negative trace
    		final Formula invariant = Formula.conjunction(invariants);
        	final String tlaCompHV = writeHistVarsSpec(tlaComp, cfgComp, invariant, true);
			// the default timeout is 5m, but can be changed via env var
        	final AlloyTrace negTrace = genNegCexTraceForCandSepInvariant(tlaCompHV, cfgNegTraces, "NT", 1, "NegTrace", NEG_TRACE_TIMEOUT);
    		formulaSeparates = !negTrace.hasError();
    		System.out.println("attempting to eliminate the following neg trace this round:");
    		System.out.println(negTrace.fullSigString());
    		System.out.println();
    		
    		// calculate the min neg trace len needed for synthesizing an assumption. we will incrementally
    		// increase it as needed.
    		final int minPartialNegTraceLen = calculatePartialTraceLen(negTrace, tlaRest, cfgRest);
    		int partialNegTraceLen = minPartialNegTraceLen;
    		if (partialNegTraceLen == -1 && !formulaSeparates) {
        		// this means that the trace /is/ allowed by 'rest', and indicates an error in the spec
    			System.out.println("The property is violated with the following trace:");
    			System.out.println(negTrace.fullSigString());
    			return "UNSAT";
    		}
        	
        	// 'dynamically' generate the init trace
        	AlloyTrace initPosTraceBuilder = defaultInitPosTrace;
        	final String badAction = negTrace.rawWord().get(partialNegTraceLen-1);
        	final String badBaseAction = badAction.replaceAll("\\..*$", "");
        	final AlloyTrace okNegPrefix = negTrace.cutToLen(minPartialNegTraceLen-1, "PT1", "PosTrace");
        	final Set<String> okNegPrefixExtensions = new ExtendTraceVisitor<>(okNegPrefix, globalActions)
        			.getTraceExtensionsByOne(tlcRest.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState());
        	final Set<String> okNegPrefixExtensionsSameBaseAction = okNegPrefixExtensions
        			.stream()
        			.filter(a -> a.indexOf(badBaseAction) == 0) // the base action must be the start of the string
        			.collect(Collectors.toSet());
        	// ideally extend the trace with an action with the same base name as the bad action
        	if (!okNegPrefixExtensionsSameBaseAction.isEmpty()) {
            	// choose best action as the one with the lowest edit distance from the bad action
        		// this is a lazy way of doing so (really should use a comparator)
        		final int minEditDist = okNegPrefixExtensionsSameBaseAction
        				.stream()
        				.map(a -> editDistance(a, badAction))
        				.min(Comparator.naturalOrder())
        				.get();
        		final String extAct = okNegPrefixExtensionsSameBaseAction
        				.stream()
        				.filter(a -> editDistance(a, badAction) == minEditDist)
        				.collect(Collectors.toList())
        				.get(0);
        		initPosTraceBuilder = extendAlloyTrace(okNegPrefix, extAct, "PT1", "PosTrace");
        	}
        	// next best is to extend the trace with any next action
        	else if (!okNegPrefixExtensions.isEmpty()) {
        		final String extAct = Utils.chooseOne(okNegPrefixExtensions);
        		initPosTraceBuilder = extendAlloyTrace(okNegPrefix, extAct, "PT1", "PosTrace");
        	}
        	else if (!okNegPrefix.isEmpty()) {
        		initPosTraceBuilder = okNegPrefix;
        	}
        	final AlloyTrace initPosTrace = initPosTraceBuilder;
        	
    		// keep track of pos traces corresponding to each env var type, as each env var type corresponds to a single
    		// formula synthesis task. these are the "current" pos traces that we will learn from (perform formula synth on).
        	long cumNumPosTraces = 1;
    		Map<Map<String,String>, List<AlloyTrace>> currentPosTraces = allEnvVarTypes
    				.stream()
    				.collect(Collectors.toMap(evt -> evt, evt -> Utils.listOf(initPosTrace)));
        	System.out.println("Init pos trace:");
        	System.out.println(initPosTrace.fullSigString());

    		// use the negative trace and all existing positive traces to generate a formula
			// keep generating positive traces until the formula turns into an invariant
    		int numFormulaSynthBatches = 0;
    		boolean foundInvariant = false;
    		while (!formulaSeparates && !foundInvariant) {
    			// compute the partial neg trace
    			final AlloyTrace partialNegTrace = negTrace.cutToLen(partialNegTraceLen);
    			System.out.println("Using the following partial neg trace for formula synth:");
        		System.out.println(partialNegTrace.fullSigString());
        		
				// synthesize new formulas
    			final int numFluents = this.useIntermediateProp ?
    					invariant.getNumFluents() + this.intermediateProp.getPastNumFluents() + 1 :
    					invariant.getNumFluents();
    			++numFormulaSynthBatches;
    			System.out.println("Formula synth batch: " + numFormulaSynthBatches);
    			final Map<Map<String,String>, Formula> evtToFormulaMap = synthesizeFormulas(partialNegTrace, currentPosTraces, numFluents, envVarTypes);
    			
    			// remove any env var type from this round that returns UNSAT. this is an optimization to prevent
    			// us from re-running workers (in a given round) that are guaranteed to return UNSAT. this modifies
    			// the out-param envVarTypes!
    			final Set<Map<String,String>> unsatEnvVarTypes = evtToFormulaMap
    					.entrySet()
    					.stream()
    					.filter(e -> e.getValue().isUNSAT())
    					.map(e -> e.getKey())
    					.collect(Collectors.toSet());
    			envVarTypes.removeAll(unsatEnvVarTypes);
    			
    			// keep track of all sat synth formulas
    			final Set<Formula> newSynthFormulas = evtToFormulaMap
    					.values()
    					.stream()
    					.filter(f -> !f.isUNSAT())
    					.collect(Collectors.toSet());
    			
    			// if all results are UNSAT then we increase the size of the partial neg trace
    			// NOTE: this does not actually imply that the formula is UNSAT, because we may only run formula synth
    			// with a subset of the env var types. we use this as a heuristic though.
    			if (newSynthFormulas.isEmpty() && partialNegTraceLen < negTrace.size()) {
                    System.out.println("All synthesized formulas are UNSAT, increasing the size of the partial neg trace");
                    System.out.println();
                    ++partialNegTraceLen;
    				numFormulaSynthBatches = 0;
                    envVarTypes = new HashSet<>(allEnvVarTypes);
                    currentPosTraces = allEnvVarTypes
            				.stream()
            				.collect(Collectors.toMap(evt -> evt, evt -> Utils.listOf(initPosTrace)));
                    continue;
    			}
    			
    			// if all results are UNSAT then we report this to the user
    			if (envVarTypes.isEmpty()) {
    				// in this case, the overall constraints are unsatisfiable so we stop and report this to the user
    				invariants.add(Formula.UNSAT());
    				return Formula.conjunction(invariants).getFormula();
    			}
    			
    			// generate positive traces to try and make the next set of formulas we synthesize invariants
    			final long fiveMinuteTimeout = 5L; // use a 5m timeout for pos traces
    			Map<Formula, AlloyTrace> newSynthFormulaResults = new HashMap<>();
				for (final Formula formula : newSynthFormulas) {
					// TODO hide this print behind a verbose flag
					System.out.println(formula);
					final String tlaRestHV = writeHistVarsSpec(tlaRest, cfgRest, formula, false);
					final AlloyTrace newPosTrace =
							genCexTraceForCandSepInvariant(tlaRestHV, cfgPosTraces, "PT", ++cumNumPosTraces, "PosTrace", fiveMinuteTimeout);
					newSynthFormulaResults.put(formula, newPosTrace);
					
					final boolean isInvariant = !newPosTrace.hasError();
					if (isInvariant) {
						break;
					}
				}
				System.out.println();
				
				// update whether an invariant has been found
				foundInvariant = newSynthFormulaResults
    					.values()
    					.stream()
    					.anyMatch(t -> !t.hasError());
    			
    			// if an invariant is found, move onto the next round. otherwise, prepare to perform formula synthesis
    			// with the new pos traces.
    			if (foundInvariant) {
    				final Set<Formula> newInvariants = newSynthFormulaResults
    						.entrySet()
    						.stream()
    						.filter(e -> !e.getValue().hasError())
    						.map(e -> e.getKey())
    						.collect(Collectors.toSet());
    				invariants.addAll(newInvariants);
    				System.out.println("Found " + newInvariants.size() + " new invariant(s) this round:");
        			for (final Formula formula : newInvariants) {
            			System.out.println(formula);
        			}
    			}
    			// no new invariants have been found during formula synth
    			else {
            		// update the set of pos traces per env var type
            		for (final Map<String,String> evt : envVarTypes) {
            			final Set<String> evtQuantTypes = evt
            					.values()
            					.stream()
            					.collect(Collectors.toSet());
            			// get the only the traces that correspond to formulas whose quantified vars have at least one
            			// type that is in this evt
            			final Set<AlloyTrace> intersectingTypeTraces = newSynthFormulaResults
            					.entrySet()
            					.stream()
            					.filter(e -> evtQuantTypes.stream().anyMatch(q -> e.getKey().containsQuantifiedType(q)))
            					.map(e -> e.getValue())
            					.collect(Collectors.toSet());
            			
            			// sanity check: we must add the evt's corresponding trace to its set of pos traces
            			if (evtToFormulaMap.containsKey(evt)) {
                			final Formula evtFormula = evtToFormulaMap.get(evt);
                			final AlloyTrace evtTrace = newSynthFormulaResults.get(evtFormula);
                			Utils.assertTrue(intersectingTypeTraces.contains(evtTrace), "");
            			}
            			
            			Set<AlloyTrace> newPosTraces = Utils.union(intersectingTypeTraces,
            					currentPosTraces.get(evt).stream().collect(Collectors.toSet()));
            			final Set<AlloyTrace> redundantTraces = newPosTraces
            					.stream()
            					// a trace t is redundant iff:
            					// \E t2 \in newPosTraces | (t2 # t) /\ t \subseteq t2
            					.filter(t -> newPosTraces.stream().anyMatch(t2 -> !t2.equals(t) && t2.contains(t)))
            					.collect(Collectors.toSet());
            			newPosTraces.removeAll(redundantTraces);
            			currentPosTraces.put(evt, newPosTraces.stream().collect(Collectors.toList()));
            		}
            		
            		// print the cumulative set of new pos traces for the user
            		final Set<AlloyTrace> allNewPosTraces = newSynthFormulaResults
							.values()
							.stream()
							.collect(Collectors.toSet());
        			System.out.println("new pos trace(s):");
        			allNewPosTraces
							.stream()
							.forEach(t -> System.out.println(t.fullSigString()));
    			}
    		}
    		System.out.println("Round " + round + " took " + timer.timeElapsedSeconds() + " seconds");
			System.out.println();
    		++round;
    	}
    	
    	// re-write the "rest" _hist file with the entire invariant. this will help the user
    	// synthesize an inductive invariant for "rest".
    	writeHistVarsSpec(tlaRest, cfgRest, Formula.conjunction(invariants), false);
    	
    	// write out the formula to a file
    	final String tlaCompBaseName = this.tlaComp.replaceAll("\\.tla", "");
    	Utils.writeFile(tlaCompBaseName + ".inv", Formula.conjunction(invariants).toJson());
    	
    	return Formula.conjunction(invariants).getFormula();
	}
	
	private AlloyTrace createInitPosTrace() {
		// create an LTS for "rest" which we will use to perform a DFS for finding the init trace
    	System.out.println("Building the LTS for the initial trace (" + tlaRest + ")");
    	PerfTimer timer = new PerfTimer();
    	tlcRest.modelCheck(tlaRest, cfgRest);
    	System.out.println("Built the LTS in " + timer.timeElapsedSeconds() + "s");
    	
    	// time the operation
		System.out.println("Creating the initial trace");
		timer = new PerfTimer();
		
		// TODO make the init trace len a param
		// TODO cap the number of iterations we can have, right now an inf loop is possible
    	int initTraceLen = 1;
    	AlloyTrace initPosTrace = new AlloyTrace();
    	while (initPosTrace.isEmpty()) {
    		InitTraceVisitor<Integer,String> visitor = new InitTraceVisitor<>(initTraceLen);
        	final List<String> initTrace = visitor.findAnInitTrace(tlcRest.getLTSBuilder().toIncompleteDetAutWithoutAnErrorState())
					.stream()
					.collect(Collectors.toList());
		    Utils.assertTrue(initTrace.size() >= initTraceLen, "requested init trace of length " + initTraceLen + " but got length " + initTrace.size());
        	initPosTrace = createAlloyTrace(initTrace, "PT1", "PosTrace");
        	++initTraceLen;
    	}
    	
    	System.out.println("Created the initial trace in " + timer.timeElapsedSeconds() + "s");
    	System.out.println();
    	return initPosTrace;
	}
	
	public AlloyTrace genCexTraceForCandSepInvariant(final String tla, final String cfg, final String trName, long trNum, final String ext, long timeout) {
		final String tlaName = tla.replaceAll("\\.tla", "");
		final String cfgName = cfg.replaceAll("\\.cfg", "");
		final String tlaFile = tlaName + ".tla";
		final String cfgFile = cfgName + ".cfg";
		final String cexTraceOutputFile = "cextrace.txt";
		
		// Step (1)
		// Call out to TLC to find a cex trace
		try {
			// TODO should use a temporary file for <cexTraceOutputFile>
			// TODO run multiple instances of TLC and choose the shortest trace
			final String[] cmd = {"sh", "-c",
					"java -jar " + TLC_JAR_PATH + " -cleanup -deadlock -workers auto -config " + cfgFile + " " + tlaFile + " > " + cexTraceOutputFile};
			Process proc = Runtime.getRuntime().exec(cmd);
			proc.waitFor(timeout, TimeUnit.MINUTES);
			
			// reached the timeout but TLC is still running--no error detected
			if (proc.isAlive()) {
				proc.destroyForcibly();
				// clean up the states dir
				final String[] rmStatesCmd = {"sh", "-c", "rm -rf states/"};
				Runtime.getRuntime().exec(rmStatesCmd);
				return new AlloyTrace();
			}

			// no error detected according to the ret code
			final int retCode = proc.exitValue();
			if (retCode == 0) {
				return new AlloyTrace();
			}
			// ret code 12 is an error trace
			if (retCode != 12) {
				System.out.println("While generating a cex trace, unexpected ret code from TLC: " + retCode);
			}
		}
		catch (Exception e) {
			e.printStackTrace();
			Utils.assertTrue(false, "Exception while generating a cex!");
		}
		
		// get the cex trace file, starting where the trace is
		return createAlloyTraceFromTlcOutput(Utils.fileContents(cexTraceOutputFile), tlaFile, cfgFile, trName, trNum, ext);
    }
	
	/**
	 * This method is similar to the previous (genNegCexTraceForCandSepInvariant) except it is specialized for generating
	 * neg traces. This method will run TLC in -continue mode and allow it to run for an extra 20% (of the time it took to
	 * reach the first cex trace). This may generate several cex traces, in which case we perform some examination to choose
	 * the "best" cex trace.
	 * @param tla
	 * @param cfg
	 * @param trName
	 * @param trNum
	 * @param ext
	 * @return
	 */
	public AlloyTrace genNegCexTraceForCandSepInvariant(final String tla, final String cfg, final String trName, int trNum, final String ext, long timeout) {
		final String tlaName = tla.replaceAll("\\.tla", "");
		final String cfgName = cfg.replaceAll("\\.cfg", "");
		final String tlaFile = tlaName + ".tla";
		final String cfgFile = cfgName + ".cfg";
		final String detectError = "Error: The behavior up to this point is:";
		
		// Call out to TLC to find a cex trace
		PerfTimer tlcTimer = new PerfTimer();
		final List<String> tlcOutputLines = new NegTraceGen().generate(tlaFile, cfgFile, detectError, timeout, TLC_JAR_PATH);
		System.out.println("TLC neg trace generation time: " + tlcTimer.timeElapsedSeconds() + " seconds");
		
		// Parse the output of TLC to create a formula that helps reproduce the error
		
		// if there is no error then we're done
		final boolean noError = tlcOutputLines
				.stream()
				.allMatch(l -> !l.contains(detectError));
		if (noError) {
			return new AlloyTrace();
		}
		
		final List<String> tlcErrorTraces = Utils.toArrayList(
				String.join("\n", tlcOutputLines).split(Pattern.quote(detectError)));
		final Set<AlloyTrace> alloyTraces = tlcErrorTraces
				.stream()
				.filter(t -> t.contains("State 1: <Initial predicate>"))
				.map(t -> {
					final List<String> lines = Utils.toArrayList(t.split("\n"));
					return createAlloyTraceFromTlcOutput(lines, tlaFile, cfgFile, trName, trNum, ext);
				})
				.collect(Collectors.toSet());
		Utils.assertTrue(!alloyTraces.isEmpty(), "alloyTraces is empty!");
		
		// only keep the min traces
		final int minLen = alloyTraces
				.stream()
				.reduce(Integer.MAX_VALUE,
						(n,t) -> Math.min(n,t.size()),
						(n1,n2) -> Math.min(n1,n2));
		System.out.println("# neg traces: " + alloyTraces.size());
		final int maxNumMinTraces = 100; // TODO
		final Set<AlloyTrace> minTraces = alloyTraces
				.stream()
				.filter(t -> t.size() == minLen)
				.limit(maxNumMinTraces)
				.collect(Collectors.toSet());
		System.out.println("# min neg traces: " + minTraces.size());
		Utils.assertTrue(!minTraces.isEmpty(), "minTraces is empty!");
		
		// only keep the min traces with the highest partial trace len
		PerfTimer partialTraceLenTimer = new PerfTimer();
		final Map<AlloyTrace,Integer> partialTraceLenMap = minTraces
				.stream()
				.collect(Collectors.toMap(t -> t, t -> calculatePartialTraceLen(t,tlaRest,cfgRest)));
		System.out.println("partial neg trace generation time: " + partialTraceLenTimer.timeElapsedSeconds() + " seconds");
		final int maxPartialTraceLen = minTraces
				.stream()
				.reduce(0,
						(n,t) -> Math.max(n, partialTraceLenMap.get(t)),
						(n1,n2) -> Math.max(n1,n2));
		final Set<AlloyTrace> maxPartialTraces = minTraces
				.stream()
				.filter(t -> partialTraceLenMap.get(t).equals(maxPartialTraceLen))
				.collect(Collectors.toSet());
		Utils.assertTrue(!maxPartialTraces.isEmpty(), "maxPartialTraces is empty!");
		
		// any one of the remaining traces will do
		return Utils.chooseOne(maxPartialTraces);
	}
	
	/**
	 * This method converts a TLC cex trace (in text format) to an AlloyTrace. This method is implemented in several steps:
	 * (1) Parse the output of TLC to create a formula that helps reproduce the error
	 * (2) Using the formula from (1), create a new TLA+ spec that efficiently reproduces the error
	 * (3) Load the new TLA+ spec as a TLC object (i.e. in Java code) and get an action-based trace, which we turn into an AlloyTrace
	 * @param tlcOutputLines
	 * @param tlaFile
	 * @param cfgFile
	 * @param trName
	 * @param trNum
	 * @param ext
	 * @return
	 */
	private AlloyTrace createAlloyTraceFromTlcOutput(final List<String> tlcOutputLines, final String tlaFile, final String cfgFile,
			final String trName, long trNum, final String ext) {
		// Step (1)
		// Parse the output of TLC to create a formula that helps reproduce the error
		
		// get the cex trace file, starting where the trace is
		final String cexTraceTxt = tlcOutputLines
				.stream()
				.dropWhile(l -> !l.equals("State 1: <Initial predicate>"))
				.collect(Collectors.joining("\n"));
		final List<String> states = Utils.toArrayList(cexTraceTxt.split("\n\n"))
				.stream()
				// only consider states in the trace (i.e. chop off the suffix of the file that doesn't contain trace info)
				.filter(s -> s.startsWith("State "))
				.map(s -> {
					// remove the "State i: ..." header
					List<String> stateLines = Utils.toArrayList(s.split("\n"));
					stateLines.remove(0);
					return String.join("\n", stateLines);
				})
				.collect(Collectors.toList());
		
		// create a formula that says: at each time step i, we must be in the corresponding state of the cex trace
		final String cexIdxVar = "cexTraceIdx";
		final String traceConstraint = IntStream.range(0, states.size())
				.mapToObj(i -> {
					final String rawState = states.get(i);
					final String stateConstraint = rawState.indent(2);
					return "/\\ " + cexIdxVar + " = " + i + " =>\n" + stateConstraint;
				})
				.collect(Collectors.joining("\n"));
		
		final String tcfName = "TraceConstraint";
		final String tcfNamePrimed = tcfName + "'";
		
		
		// Step (2)
		// Using the formula from (1), create a new TLA+ spec that efficiently reproduces the error
		
		// use the original TLA+ file to construct the reproducer spec
		TLC tlc = new TLC();
		tlc.initialize(tlaFile, cfgFile);

    	final FastTool ft = (FastTool) tlc.tool;
		final String moduleName = tlc.getModelName();
		final ModuleNode mn = ft.getModule(moduleName);
		final List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
				.stream()
				// only retain module for the .tla file
				.filter(d -> moduleName.equals(d.getOriginallyDefinedInModuleNode().getName().toString()))
				.filter(d -> !d.getName().toString().equals("vars")) // remove the vars decl; we insert this manually
				.collect(Collectors.toList());
		
		List<String> strModuleNodes = moduleNodes
				.stream()
				.map(d -> {
					final String dname = d.getName().toString();
					if (tlc.actionsInSpec().contains(dname)) {
						d.addConjunct(cexIdxVar + "' = " + cexIdxVar + " + 1");
						d.addConjunct(tcfNamePrimed);
					}
					else if (dname.equals("Init")) {
						d.addConjunct(cexIdxVar + " = 0");
						d.addConjunct(tcfName);
					}
					return d;
				 })
				.map(d -> d.toTLA())
				.collect(Collectors.toList());
		
		// add <traceConstraint> to the module definitions
		final Set<String> allTypes = actionParamTypes
				.values()
				.stream()
				.reduce((Set<String>)new HashSet<String>(),
						(acc,l) -> Utils.union(acc, l.stream().collect(Collectors.toSet())),
						(l1,l2) -> Utils.union(l1,l2));
		
		Set<OpDefNode> dependencyNodes = moduleNodes
				.stream()
				.filter(d -> allTypes.contains(d.getName().toString()))
				.collect(Collectors.toSet());
		
		for (int i = 0; i < moduleNodes.size(); ++i) {
			final OpDefNode defNode = moduleNodes.get(i);
			if (dependencyNodes.isEmpty()) {
				strModuleNodes.add(i, tcfName + " ==\n" + traceConstraint);
				break;
			}
			else if (dependencyNodes.contains(defNode)) {
				dependencyNodes.remove(defNode);
			}
			Utils.assertTrue(i < moduleNodes.size()-1, "Could not find a place for " + tcfName + "!");
		}
		
		final Set<String> sortConsts = this.sortElementsMap.values()
				.stream()
				.reduce((Set<String>)new HashSet<String>(),
						(acc,l) -> Utils.union(acc, l.stream().collect(Collectors.toSet())),
						(l1,l2) -> Utils.union(l1,l2));
		final Set<String> allConsts = Utils.union(sortConsts, tlc.constantsInSpec().stream().collect(Collectors.toSet()));
		
		// construct the spec
		final String specName = "CexTrace";
		final String specBody = String.join("\n\n", strModuleNodes);
		
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        final List<String> moduleWhiteList =
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals", "Randomization",
        				"NaturalsInduction", "RealTime", "Sequences", "SequencesExt", "TLC", "TLCExt");
        ArrayList<String> moduleNameList = Utils.filterArrayWhiteList(moduleWhiteList, ft.getModuleNames());
        // ensure that the naturals are included so we can increment the cexIdxVar
        if (!moduleNameList.contains("Naturals")) {
        	moduleNameList.add("Naturals");
        }
        // ensure that TLC is included for the definition of @@
        if (!moduleNameList.contains("TLC")) {
        	moduleNameList.add("TLC");
        }
        
        final Set<String> stateVars = Utils.union(tlc.stateVarsInSpec(), Utils.setOf(cexIdxVar));

        final String moduleList = String.join(", ", moduleNameList);
        final String constantsDecl = "CONSTANTS " + String.join(", ", allConsts);
        final String varList = String.join(", ", stateVars);
        final String modulesDecl = moduleList.isEmpty() ? "" : "EXTENDS " + moduleList;
        final String varsDecl = "VARIABLES " + varList;
        final String varsListDecl = "vars == <<" + varList + ">>";
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(modulesDecl).append("\n");
        builder.append("\n");
        builder.append(constantsDecl).append("\n");
        builder.append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(varsListDecl).append("\n");
        builder.append("\n");
        builder.append(specBody);
        builder.append("\n");
        builder.append(endModule).append("\n");

        final String cexTraceTla = specName + ".tla";
        Utils.writeFile(cexTraceTla, builder.toString());
        
        // create the config file for the TLA+ reproducer
        StringBuilder cfgBuilder = new StringBuilder();
        final String cfgContent = String.join("\n", Utils.fileContents(cfgFile)) + "\n";
        cfgBuilder.append(cfgContent);
        cfgBuilder.append("CONSTANTS\n");
        sortConsts.stream()
        		.filter(c -> !Utils.isIntegerString(c))
        		.forEach(c -> {
                	final String constAssg = c + "=" + c + "\n";
                	cfgBuilder.append(constAssg);
        		});
        final String cexTraceCfg = specName + ".cfg";
        Utils.writeFile(cexTraceCfg, cfgBuilder.toString());
		
        
        // Step (3)
        // Load the new TLA+ spec as a TLC object (i.e. in Java code) and get an action-based trace, which we turn into an AlloyTrace
    	TLC tlcCexReproducer = new TLC();
    	tlcCexReproducer.modelCheck(cexTraceTla, cexTraceCfg);
    	final LTS<Integer, String> lts = tlcCexReproducer.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	Utils.assertTrue(!SafetyUtils.INSTANCE.ltsIsSafe(lts), "Couldn't reproduce TLC error!");
		
		// if candSep isn't an invariant, return a trace that should be covered by the formula
    	final int numTraces = 1; // only generate one trace at a time
    	final Set<List<String>> errTraces = MultiTraceCex.INSTANCE.findErrorTraces(lts, numTraces, this.tlcComp.actionsInSpec());
		Utils.assertTrue(errTraces.size() == 1, "expected one err trace but there were " + errTraces.size());
		final List<String> errTrace = Utils.chooseOne(errTraces);
		final String name = trName + trNum;
		
		return createAlloyTrace(errTrace, name, ext);
	}
	
	private int cachedCalculatePartialTraceLen(final AlloyTrace trace, final String tla, final String cfg) {
		for (int i = 1; i < trace.size(); ++i) {
			final AlloyTrace partialTrace = trace.cutToLen(i);
			
			// calculate <isTraceInSpec>
			boolean isTraceInSpec = false;
			final Utils.Pair<AlloyTrace,String> cacheKey = new Utils.Pair<>(partialTrace,tla);
			if (traceInSpecCache.containsKey(cacheKey)) {
				isTraceInSpec = traceInSpecCache.get(cacheKey);
			}
			else {
				isTraceInSpec = isTraceInSpec(partialTrace,tla,cfg);
				traceInSpecCache.put(cacheKey, isTraceInSpec);
			}
			
			// use <isTraceInSpec>
			if (!isTraceInSpec) {
				return i;
			}
		}
		return -1;
	}
	
	private int calculatePartialTraceLen(final AlloyTrace trace, final String tla, final String cfg) {
		for (int i = 1; i < trace.size(); ++i) {
			final AlloyTrace partialTrace = trace.cutToLen(i);
			if (!isTraceInSpec(partialTrace,tla,cfg)) {
				return i;
			}
		}
		return -1;
	}
	
	private boolean isTraceInSpec(final AlloyTrace trace, final String tla, final String cfg) {
		final String tlaName = tla.replaceAll("\\.tla", "");
		final String cfgName = cfg.replaceAll("\\.cfg", "");
		final String tlaFile = tlaName + ".tla";
		final String cfgFile = cfgName + ".cfg";
		
		// create a formula that says: at each time step i, we must take action i in <trace> (the given AlloyTrace)
		final String cexIdxVar = "cexTraceIdx";
		final String errVar = "err";
		final String inTraceConstraint = IntStream.range(0, trace.size())
				.mapToObj(i -> {
					final String act = trace.tlaTrace().get(i);
					final String errVarChange = i < trace.size()-1 ? errVar+"' = "+errVar : errVar+"' = TRUE";
					return "/\\ " + cexIdxVar + " = " + i + " => " + act + " /\\ " + errVarChange;
				})
				.collect(Collectors.joining("\n"));
		final String outTraceConstraint = "/\\ " + cexIdxVar + " >= " + trace.size() + " => FALSE";
		final String traceConstraint = inTraceConstraint + "\n" + outTraceConstraint;
		
		// use the original TLA+ file to construct the reproducer spec
		TLC tlc = new TLC();
		tlc.initialize(tlaFile, cfgFile);

    	final FastTool ft = (FastTool) tlc.tool;
		final String moduleName = tlc.getModelName();
		final ModuleNode mn = ft.getModule(moduleName);
		final List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
				.stream()
				// only retain module for the .tla file
				.filter(d -> moduleName.equals(d.getOriginallyDefinedInModuleNode().getName().toString()))
				.filter(d -> !d.getName().toString().equals("vars")) // remove the vars decl; we insert this manually
				.collect(Collectors.toList());
		
		List<String> strModuleNodes = moduleNodes
				.stream()
				.map(d -> {
					final String dname = d.getName().toString();
					final boolean isInternalAct = !this.tlcComp.actionsInSpec().contains(dname);
					if (tlc.actionsInSpec().contains(dname)) {
						if (isInternalAct) {
							d.addConjunct(cexIdxVar + "' = " + cexIdxVar);
						} else {
							d.addConjunct(cexIdxVar + "' = " + cexIdxVar + " + 1");
						}
					}
					else if (dname.equals("Init")) {
						d.addConjunct(cexIdxVar + " = 0");
						d.addConjunct(errVar + " = FALSE");
					}
					return d;
				 })
				.map(d -> d.toTLA())
				.collect(Collectors.toList());
		
		// add the trace constraint and the new spec decl to the list of muldes
		final String tcfName = "TraceConstraint";
		final String tcfSpecName = "TraceConstraintSpec";
		final String traceConstraintDecl = tcfName + " ==\n" + traceConstraint;
		final String internalActionDecl = "InternalAction == UNCHANGED<<cexTraceIdx,err>>";
		final String specVarDecl = tcfSpecName + " == Init /\\ [][Next /\\ (" + tcfName + " \\/ InternalAction)]_vars";
		strModuleNodes.add(traceConstraintDecl);
		strModuleNodes.add(internalActionDecl);
		strModuleNodes.add(specVarDecl);
		
		// gather all the consts
		final Set<String> sortConsts = this.sortElementsMap.values()
				.stream()
				.reduce((Set<String>)new HashSet<String>(),
						(acc,l) -> Utils.union(acc, l.stream().collect(Collectors.toSet())),
						(l1,l2) -> Utils.union(l1,l2));
		final Set<String> allConsts = Utils.union(sortConsts, tlc.constantsInSpec().stream().collect(Collectors.toSet()));
		
		// construct the spec
		final String specName = "CexTrace";
		final String specBody = String.join("\n\n", strModuleNodes);
		
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        final List<String> moduleWhiteList =
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals", "Randomization",
        				"NaturalsInduction", "RealTime", "Sequences", "SequencesExt", "TLC", "TLCExt");
        ArrayList<String> moduleNameList = Utils.filterArrayWhiteList(moduleWhiteList, ft.getModuleNames());
        // ensure that the naturals are included so we can increment the cexIdxVar
        if (!moduleNameList.contains("Naturals")) {
        	moduleNameList.add("Naturals");
        }
        // ensure that TLC is included for the definition of @@
        if (!moduleNameList.contains("TLC")) {
        	moduleNameList.add("TLC");
        }
		
		final String noErrsInv = "NoErr";
		final String invariantDecl = noErrsInv + " == " + errVar + " = FALSE";
        
        final Set<String> stateVars = Utils.union(tlc.stateVarsInSpec(), Utils.setOf(cexIdxVar,errVar));

        final String moduleList = String.join(", ", moduleNameList);
        final String constantsDecl = "CONSTANTS " + String.join(", ", allConsts);
        final String varList = String.join(", ", stateVars);
        final String modulesDecl = moduleList.isEmpty() ? "" : "EXTENDS " + moduleList;
        final String varsDecl = "VARIABLES " + varList;
        final String varsListDecl = "vars == <<" + varList + ">>";
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(modulesDecl).append("\n");
        builder.append("\n");
        builder.append(constantsDecl).append("\n");
        builder.append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(varsListDecl).append("\n");
        builder.append("\n");
        builder.append(invariantDecl);
        builder.append("\n\n");
        builder.append(specBody);
        builder.append("\n");
        builder.append(endModule).append("\n");

        final String traceInSpecTla = specName + ".tla";
        Utils.writeFile(traceInSpecTla, builder.toString());
        
        // create the config file for the TLA+ reproducer
        StringBuilder cfgBuilder = new StringBuilder();
        final List<String> cfgLines = Utils.fileContents(cfgFile)
        		.stream()
        		.filter(l -> !l.contains("SPECIFICATION"))
        		.filter(l -> !l.contains("INVARIANT"))
        		.collect(Collectors.toList());
        final String cfgContent = String.join("\n", cfgLines) + "\nSPECIFICATION " + tcfSpecName + "\nINVARIANT " + noErrsInv + "\n";
        cfgBuilder.append(cfgContent);
        cfgBuilder.append("CONSTANTS\n");
        sortConsts.stream()
        		.filter(c -> !Utils.isIntegerString(c))
        		.forEach(c -> {
                	final String constAssg = c + "=" + c + "\n";
                	cfgBuilder.append(constAssg);
        		});
        final String traceInSpecCfg = specName + ".cfg";
        Utils.writeFile(traceInSpecCfg, cfgBuilder.toString());

        // run the spec and see if there is an error. the trace appears in the spec iff there is an error
        // use iterative deepening 
        final String[] cmd = {"java", "-jar", TLC_JAR_PATH, "-cleanup", "-deadlock", "-dfid", "100", "-config", traceInSpecCfg, traceInSpecTla};
		try {
			Process proc = Runtime.getRuntime().exec(cmd);
			final long timeout = 10L;
			proc.waitFor(timeout, TimeUnit.SECONDS);
			if (proc.isAlive()) {
				// if TLC is still going then it hasn't found an error yet
				proc.destroyForcibly();
				return false;
			}
			final int retCode = proc.exitValue();
			
			// ret code 0 is no err and 12 is an error trace
			Utils.assertTrue(retCode == 0 || retCode == 12, "Trace is in a spec, unexpected ret code from TLC: " + retCode +
					" (" + traceInSpecTla + ", " + traceInSpecCfg + ")");
			final boolean error = retCode == 12;
			return error;
		}
		catch (IOException | InterruptedException e) {
			Utils.assertTrue(false, "Error while testing whether a trace is in a spec");
		}
		
		// unreachable code to satisfy the compiler
		Utils.assertTrue(false, "Should not reach here!");
		return false;
	}
	
	private AlloyTrace createAlloyTrace(final List<String> word, final String name, final String ext) {
		// use the alphabet for the component
		final Set<String> alphabet = this.tlcComp.actionsInSpec();
		final List<String> trace = word
				.stream()
				.filter(act -> {
					final String abstractAct = act.replaceAll("\\..*$", "");
					return alphabet.contains(abstractAct);
				})
				.map(a -> {
					return Utils.toArrayList(a.split("\\."))
							.stream()
							.map(p -> Utils.toArrayList(p.replaceAll("[{}]", "").split(","))) // conc act -> list of conc params
							.map(l -> sanitizeTokensForAlloy(l)) // sanitize each param so it can be encoded in an Alloy file
							.collect(Collectors.joining());
				})
				.collect(Collectors.toList());
		final List<String> tlaTrace = word
				.stream()
				.filter(act -> {
					final String abstractAct = act.replaceAll("\\..*$", "");
					return alphabet.contains(abstractAct);
				})
				.map(a -> {
					final List<String> actParts = Utils.toArrayList(a.split("\\."));
					Utils.assertTrue(actParts.size() >= 1, "eror splitting an action!");
					final String act = actParts.get(0);
					final List<String> params = actParts.subList(1, actParts.size());
					return params.size() == 0 ? act : act + "(" + String.join(",", params) + ")";
				})
				.collect(Collectors.toList());
		return new AlloyTrace(trace, tlaTrace, word, name, ext);
	}
	
	private AlloyTrace extendAlloyTrace(final AlloyTrace trace, final String extAct, final String name, final String ext) {
		List<String> newWord = new ArrayList<>(trace.rawWord());
		newWord.add(extAct);
		return createAlloyTrace(newWord, name, ext);
	}
	
	private Map<Map<String,String>, Formula> synthesizeFormulas(final AlloyTrace negTrace,
			final Map<Map<String,String>, List<AlloyTrace>> posTraces, final int curNumFluents, Set<Map<String,String>> envVarTypes) {
		FormulaSynth formSynth = new FormulaSynth(this.seed);
		return formSynth.synthesizeFormulas(envVarTypes, negTrace, posTraces,
				tlcComp, internalActions, sortElementsMap, setSortElementsMap, actionParamTypes, maxActParamLen,
				qvars, legalEnvVarCombos, curNumFluents);
	}
	
	private String writeHistVarsSpec(final String tla, final String cfg, final Formula candSep, boolean candSepInActions) {
		final String noExt = "";
		return writeHistVarsSpec(tla, cfg, candSep, candSepInActions, noExt);
	}
	
	private String writeHistVarsSpec(final String tla, final String cfg, final Formula candSep, boolean candSepInActions, final String ext) {
    	final String tlaCompBaseName = tla.replaceAll("\\.tla", "");
    	final String specName = tlaCompBaseName + "_hist" + ext;
    	
		TLC tlc = new TLC();
		tlc.initialize(tla, cfg);

    	final FastTool ft = (FastTool) tlc.tool;
		final String moduleName = tlc.getModelName();
		final ModuleNode mn = ft.getModule(moduleName);
		final List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
				.stream()
				// only retain module for the .tla file
				.filter(d -> moduleName.equals(d.getOriginallyDefinedInModuleNode().getName().toString()))
				.filter(d -> !d.getName().toString().equals("vars")) // remove the vars decl; we insert this manually
				.collect(Collectors.toList());
		
		List<String> strModuleNodes = moduleNodes
				.stream()
				.map(d -> {
					final String dname = d.getName().toString();
					if (tlc.actionsInSpec().contains(dname)) {
						d.addFluentVars(candSep, candSepInActions);
						if (this.useIntermediateProp) {
							d.addFluentVars(this.intermediateProp, candSepInActions);
						}
					}
					else if (dname.equals("Init")) {
						d.addFluentInitVars(candSep);
						if (this.useIntermediateProp) {
							d.addFluentInitVars(this.intermediateProp);
						}
					}
					return d;
				 })
				.map(d -> d.toTLA())
				.collect(Collectors.toList());
		
		// add CandSep to the module definitions (after any dependencies, where a dependency
		// is a definition for a type symbol that occurs in CandSep)
		final Set<String> allTypes = actionParamTypes
				.values()
				.stream()
				.reduce((Set<String>)new HashSet<String>(),
						(acc,l) -> Utils.union(acc, l.stream().collect(Collectors.toSet())),
						(l1,l2) -> Utils.union(l1,l2));
		
		Set<OpDefNode> candSepDependencyNodes = moduleNodes
				.stream()
				.filter(d -> allTypes.contains(d.getName().toString()))
				.collect(Collectors.toSet());
		
		for (int i = 0; i < moduleNodes.size(); ++i) {
			final OpDefNode defNode = moduleNodes.get(i);
			if (candSepDependencyNodes.isEmpty()) {
				strModuleNodes.add(i, "CandSep ==\n" + candSep.getFormula());
				break;
			}
			else if (candSepDependencyNodes.contains(defNode)) {
				candSepDependencyNodes.remove(defNode);
			}
			Utils.assertTrue(i < moduleNodes.size()-1, "Could not find a place for CandSep!");
		}
		
		// add the safety property in (if one is provided)
		// only include the safety property when writing negative traces, i.e. when candSepInActions is true
		final String safetyDecl = !(this.useIntermediateProp && candSepInActions) ? "" :
			"\nSafety ==\n" + this.intermediateProp.getFormula() + "\n";
		
		// construct the spec
		final String specBody = String.join("\n\n", strModuleNodes);
		
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        final List<String> moduleWhiteList =
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals", "Randomization",
        				"NaturalsInduction", "RealTime", "Sequences", "SequencesExt", "TLC", "TLCExt");
        ArrayList<String> moduleNameList = Utils.filterArrayWhiteList(moduleWhiteList, ft.getModuleNames());
        
        final Set<String> stateVars = this.useIntermediateProp ?
        		Utils.union(tlc.stateVarsInSpec(), candSep.getFluentVars(), this.intermediateProp.getFluentVars()) :
            	Utils.union(tlc.stateVarsInSpec(), candSep.getFluentVars());

        final String moduleList = String.join(", ", moduleNameList);
        final String constantsDecl = tlc.constantsInSpec().isEmpty() ? "" : "CONSTANTS " + String.join(", ", tlc.constantsInSpec());
        final String varList = String.join(", ", stateVars);
        final String modulesDecl = moduleList.isEmpty() ? "" : "EXTENDS " + moduleList;
        final String varsDecl = "VARIABLES " + varList;
        final String varsListDecl = "vars == <<" + varList + ">>";
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(modulesDecl).append("\n");
        builder.append("\n");
        builder.append(constantsDecl).append("\n");
        builder.append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(varsListDecl).append("\n");
        builder.append("\n");
        builder.append(specBody);
        builder.append("\n");
        builder.append(safetyDecl);
        builder.append(endModule).append("\n");

        final String fileName = specName + ".tla";
        final String file = fileName;
        Utils.writeFile(file, builder.toString());
        
        return specName;
	}
	
	
	/* Helper methods */
	
	private static Set<List<String>> linePermutations(Set<List<String>> set, List<String> line) {
		if (line.isEmpty()) {
			return set;
		}
		final String elem = line.remove(0);
		final Set<List<String>> partial = linePermutations(set, line);
		Set<List<String>> combined = new HashSet<>();
		for (List<String> l : partial) {
			for (int i = 0; i <= l.size(); ++i) {
				List<String> combList = new ArrayList<>(l);
				combList.add(i, elem);
				combined.add(combList);
			}
		}
		return combined;
	}
	
	private static Set<Map<String,String>> setPermutations(final Set<String> set) {
		final Set<List<String>> linePerms =
				linePermutations(Utils.setOf(new ArrayList<>()), set.stream().collect(Collectors.toList()));
		final List<String> canonOrder = set.stream().collect(Collectors.toList());
		Utils.assertTrue(linePerms.stream().allMatch(l -> l.size()==canonOrder.size()), "Invalid size of a line perm");
		
		Set<Map<String,String>> permutations = new HashSet<>();
		for (final List<String> linePerm : linePerms) {
			Map<String,String> mapPerm = new HashMap<>();
			for (int i = 0; i < linePerm.size(); ++i) {
				final String key = canonOrder.get(i);
				final String val = linePerm.get(i);
				mapPerm.put(key,val);
			}
			permutations.add(mapPerm);
		}
		return permutations;
	}
	
	/**
	 * Returns a map where the key is the sort name and the value is the set of all
	 * permutations of the sort elements.
	 * @return
	 */
	private Map<String, Set<Map<String,String>>> permutationsPerSort() {
		return sortElementsMap
				.entrySet()
				.stream()
				.map(e -> new Utils.Pair<>(e.getKey(), setPermutations(e.getValue())))
				.collect(Collectors.toMap(p -> p.first, p -> p.second));
	}
	
	/**
	 * Returns a set of all permutations across all sorts.
	 * @return
	 */
	private Set<Map<String,String>> calcAllPermutations() {
		Set<Map<String,String>> allPerms = new HashSet<>();
		allPerms.add(new HashMap<>());

		final Map<String, Set<Map<String,String>>> permsPerSort = permutationsPerSort();
		for (final Set<Map<String,String>> sortPerms : permsPerSort.values()) {
			Set<Map<String,String>> sortCombPerms = new HashSet<>();
			for (final Map<String,String> sortPerm : sortPerms) {
				for (Map<String,String> partialPerm : allPerms) {
					Map<String,String> combPerm = new HashMap<>(partialPerm);
					combPerm.putAll(sortPerm);
					sortCombPerms.add(combPerm);
				}
			}
			allPerms = sortCombPerms;
		}
		return allPerms;
	}
	
	/**
	 * The assumption is that the act has each param sanitized and separated by dots.
	 * We return permutations in the same format.
	 * @param act
	 * @return
	 */
	private Set<String> actionPermutations(final String act) {
		final List<String> parts = Utils.toArrayList(act.split("\\."));
		Utils.assertTrue(!parts.isEmpty(), "expected a nonempty list, but got: " + parts);
		final String base = parts.get(0);
		final List<String> params = parts.subList(1, parts.size());
		return this.allPermutations
				.stream()
				.map(perm -> {
					return params
							.stream()
							// TODO delete this
							//.map(param -> sanitizeTokensForAlloy(Utils.listOf(param)))
							.map(param -> perm.get(param))
							.collect(Collectors.toList());
				})
				// pl = permuted list (of params)
				.map(pl -> base + "." + String.join(".", pl))
				.collect(Collectors.toSet());
	}
	
	//private Set<AlloyTrace> tracePermutations(final AlloyTrace trace) {
	//}
	
	private Set<String> actionPermutationReduction(final Set<String> set) {
		Set<String> reduced = new HashSet<>();
		Set<String> permutationsFound = new HashSet<>();
		for (final String elem : set) {
			if (!permutationsFound.contains(elem)) {
				reduced.add(elem);
				permutationsFound.addAll(actionPermutations(elem));
			}
		}
		return reduced;
	}
	
	private Set<Map<String,String>> createAllEnvVarTypes(final Set<String> allTypes) {
		return createAllEnvVarTypes(allTypes, new HashMap<>(), new HashMap<>());
	}
	
	private Set<Map<String,String>> createAllEnvVarTypes(final Set<String> allTypes, Map<String,String> envTypes,
			Map<String,Integer> envTypeCounts) {
		Set<Map<String,String>> cumEnvVarTypes = new HashSet<>();
		
		// base case
		final boolean allVarsAssigned = this.qvars
				.stream()
				.allMatch(v -> envTypes.containsKey(v)); // is v assigned a value?
		if (allVarsAssigned) {
			cumEnvVarTypes.add(envTypes);
			return cumEnvVarTypes;
		}
		
		for (final String type : allTypes) {
			final int numTimesTypeUsedInEnv = envTypeCounts.getOrDefault(type, 0);
			if (numTimesTypeUsedInEnv < maxNumVarsPerType) {
				// for each var that hasn't already been assigned a type, assign it to <type>
				final Set<String> unassignedVars = this.qvars
						.stream()
						.filter(v -> !envTypes.containsKey(v))
						.collect(Collectors.toSet());
				for (final String var : unassignedVars) {
					Map<String,String> newEnvTypes = new HashMap<>(envTypes);
					newEnvTypes.put(var, type);
					Map<String,Integer> newEnvTypeCounts = new HashMap<>(envTypeCounts);
					newEnvTypeCounts.put(type, numTimesTypeUsedInEnv+1);
					
					final Set<Map<String,String>> partialEnvVarTypes = createAllEnvVarTypes(allTypes, newEnvTypes, newEnvTypeCounts);
					cumEnvVarTypes.addAll(partialEnvVarTypes);
				}
			}
		}
		
		return cumEnvVarTypes;
	}
	
	private static Map<String, Set<String>> createSortElementsMap(TLC tlc, boolean sanitize) {
		// create a map of sort -> elements (elements = atoms)
		Map<String, Set<String>> sortElements = new HashMap<>();
		for (final List<String> constList : tlc.tool.getModelConfig().getConstantsAsList()) {
			if (constList.size() == 2) {
				// constList is a CONSTANT assignment
				final String sort = constList.get(0);
				final Set<String> elems = parseElements(constList.get(1), sanitize);
				sortElements.put(sort, elems);
			}
		}
		return sortElements;
	}
	
	/**
	 * We expect <rawElems> to encode a set. If it doesn't, we throw.
	 * @param rawElems
	 * @return
	 */
	private static Set<String> parseElements(final String rawSet, boolean sanitize) {
		final String trimmedRawSet = rawSet.trim(); // to be extra defensive
		final char rawSetFirstChar = trimmedRawSet.charAt(0);
		final char rawSetLastChar = trimmedRawSet.charAt(trimmedRawSet.length()-1);
		Utils.assertTrue(rawSetFirstChar == '{' && rawSetLastChar == '}',
				"Sorts must be sets of elements; encountered not set value: " + rawSet);
		
		final String rawElems = trimmedRawSet.substring(1, trimmedRawSet.length()-1).trim();
		final List<String> tokens = Utils.toArrayList(rawElems.split(" "))
				.stream()
				.filter(e -> !e.equals(","))
				.collect(Collectors.toList());
		
		final List<List<String>> tokenGroups = createTokenGroups(tokens);
		return tokenGroups
				.stream()
				.map(g -> sanitize ? sanitizeTokensForAlloy(g) : recreateRawToken(g))
				.collect(Collectors.toSet());
	}
	
	private static List<List<String>> createTokenGroups(final List<String> tokens) {
		List<List<String>> groups = new ArrayList<>();
		int parenDepth = 0;
		List<String> curGroup = new ArrayList<>();
		for (int i = 0; i < tokens.size(); ++i) {
			final String tok = tokens.get(i);
			final boolean isLeftParen = tok.equals("{");
			final boolean isRightParen = tok.equals("}");
			
			// if the token is a curly brace (I'm overloading "curly brace" as "paren")
			if (isLeftParen) {
				++parenDepth;
			}
			else if (isRightParen) {
				--parenDepth;
			}
			else {
				// if it's not a paren, add it to the current token group
				curGroup.add(tok);
			}
			
			// when the parens are balanced we've completed a new token group
			if (parenDepth == 0) {
				groups.add(curGroup);
				curGroup = new ArrayList<>();
			}
		}
		return groups;
	}
	
	/**
	 * this code stub will ensure that curly braces and numbers are in a format where
	 * they can be correctly used in an Alloy file.
	 * @param toks
	 * @return
	 */
	private static String sanitizeTokensForAlloy(final List<String> toks) {
		if (toks.isEmpty()) {
			return "";
		}
		final boolean isSet = toks.size() > 1;
		if (isSet) {
			final String toksStr = toks
					.stream()
					.map(t -> t.trim())
					.collect(Collectors.joining());
			// add underscores to mark sets
			return "_" + toksStr + "_";
		} else {
			final String elem = toks.get(0).trim();
			// precede numbers with "NUM" to get the Alloy file to compile
			return elem.matches("[0-9]+") ? "NUM"+elem : elem;
		}
	}
	
	private static String recreateRawToken(final List<String> toks) {
		if (toks.isEmpty()) {
			return "";
		}
		final boolean isSet = toks.size() > 1;
		if (isSet) {
			final String toksStr = toks
					.stream()
					.map(t -> t.trim())
					.collect(Collectors.joining(","));
			return "{" + toksStr + "}";
		} else {
			final String elem = toks.get(0).trim();
			return elem;
		}
	}

	
	/* The fact that the following methods are a huge copy-pasta is really not great */
	
	private static Map<String, Map<String, Set<String>>> createSetSortElementsMap(TLC tlc) {
		// create a map of sort -> elements -> elements (elements = atoms)
		Map<String, Map<String, Set<String>>> setSortElements = new HashMap<>();
		for (final List<String> constList : tlc.tool.getModelConfig().getConstantsAsList()) {
			if (constList.size() == 2) {
				// constList is a CONSTANT assignment
				final String sort = constList.get(0);
				final Map<String, Set<String>> elems = parseSetElements(constList.get(1));
				if (elems != null) {
					setSortElements.put(sort, elems);
				}
			}
		}
		return setSortElements;
	}
	
	/**
	 * We expect <rawElems> to encode a set. If it doesn't, we throw.
	 * @param rawElems
	 * @return
	 */
	private static Map<String, Set<String>> parseSetElements(final String rawSet) {
		final String trimmedRawSet = rawSet.trim(); // to be extra defensive
		final char rawSetFirstChar = trimmedRawSet.charAt(0);
		final char rawSetLastChar = trimmedRawSet.charAt(trimmedRawSet.length()-1);
		Utils.assertTrue(rawSetFirstChar == '{' && rawSetLastChar == '}',
				"Sorts must be sets of elements; encountered not set value: " + rawSet);
		
		final String rawElems = trimmedRawSet.substring(1, trimmedRawSet.length()-1).trim();
		final List<String> tokens = Utils.toArrayList(rawElems.split(" "))
				.stream()
				.filter(e -> !e.equals(","))
				.collect(Collectors.toList());
		
		final List<List<String>> tokenGroups = createTokenGroups(tokens);
		final boolean isSetSort = tokenGroups
				.stream()
				.anyMatch(g -> g.size() > 1);
		
		// signal that this isn't a set sort (sort of sets)
		if (!isSetSort) {
			return null;
		}
		
		// return a map of sort element (a set) to its set members
		Map<String, Set<String>> setElements = new HashMap<>();
		for (final List<String> toks : tokenGroups) {
			final String set = sanitizeTokensForAlloy(toks);
			final Set<String> setElems = toks
					.stream()
					.map(t -> sanitizeTokensForAlloy(Utils.listOf(t)))
					.collect(Collectors.toSet());
			setElements.put(set, setElems);
		}
		
		return setElements;
	}
	
	// thank you: https://www.baeldung.com/java-levenshtein-distance
	private static int editDistance(String x, String y) {
	    int[][] dp = new int[x.length() + 1][y.length() + 1];

	    for (int i = 0; i <= x.length(); i++) {
	        for (int j = 0; j <= y.length(); j++) {
	            if (i == 0) {
	                dp[i][j] = j;
	            }
	            else if (j == 0) {
	                dp[i][j] = i;
	            }
	            else {
	                dp[i][j] = edMin(dp[i - 1][j - 1] 
	                 + edCostOfSubstitution(x.charAt(i - 1), y.charAt(j - 1)), 
	                  dp[i - 1][j] + 1, 
	                  dp[i][j - 1] + 1);
	            }
	        }
	    }

	    return dp[x.length()][y.length()];
	}

	private static int edCostOfSubstitution(char a, char b) {
        return a == b ? 0 : 1;
    }

	private static int edMin(int... numbers) {
        return Arrays.stream(numbers)
          .min().orElse(Integer.MAX_VALUE);
    }
}

