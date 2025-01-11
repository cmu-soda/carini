package recomp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.TimeUnit;
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
	private static final int INIT_MAX_POS_TRACES = 6;
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
	private final Set<String> internalActions;
	private final Map<String, Set<String>> sortElementsMap;
	private final Map<String, Map<String, Set<String>>> setSortElementsMap;
	private final Map<String, List<String>> actionParamTypes;
	private final int maxActParamLen;
	private final int maxNumVarsPerType;
	private final Set<String> qvars;
	private final Set<Set<String>> legalEnvVarCombos;
	private final Random seed;
	
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
    	
    	// the actions that internal to "component". it is fine to include formulas over actions that
		// are internal to "rest" so we don't mark those as "internal".
    	internalActions = Utils.setMinus(tlcComp.actionsInSpec(), tlcRest.actionsInSpec());
    	
    	// obtain a map of: sort -> Set(elements/atoms in the sort)
    	sortElementsMap = createSortElementsMap(tlcSys);
    	
    	// obtain a map of: sort -> Set(elements/atoms in the sort) -> Set(elements/atoms in each set in the sort)
    	setSortElementsMap = createSetSortElementsMap(tlcSys);
		
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
		final Set<String> allTypes = this.actionParamTypes.values()
				.stream()
				.map(l -> l.stream().collect(Collectors.toSet()))
				.reduce((Set<String>)new HashSet<String>(),
						(acc,s) -> Utils.union(acc, s),
						(s1,s2) -> Utils.union(s1, s2));
		final Set<Map<String,String>> allEnvVarTypes = createAllEnvVarTypes(allTypes);
		Utils.assertTrue(!allEnvVarTypes.isEmpty(), "internal error: envVarTypes is empty!");
    	
		// keep track of pos traces corresponding to each env var type, as each env var type corresponds to a single
		// formula synthesis task. we initialize the map with <initPosTrace> for every env var type. these are the
    	// "current" pos traces that we will learn from (perform formula synth on).
    	final AlloyTrace initPosTrace = createInitPosTrace();
		Map<Map<String,String>, List<AlloyTrace>> currentPosTraces = allEnvVarTypes
				.stream()
				.collect(Collectors.toMap(evt -> evt, evt -> Utils.listOf(initPosTrace)));
    	
    	// keep track of the max num pos traces (per env var type) that we'll allow during formula synthesis
		Map<Map<String,String>, Integer> maxNumPosTraces = allEnvVarTypes
				.stream()
				.collect(Collectors.toMap(evt -> evt, evt -> INIT_MAX_POS_TRACES));
    	
    	// keep track of the number of duplicate traces in each round (per env var type). this will help us increment
    	// <maxNumPosTraces> appropriately.
		Map<Map<String,String>, Integer> numDuplicateTracesPerRound = allEnvVarTypes
				.stream()
				.collect(Collectors.toMap(evt -> evt, evt -> 0));
    	
    	// collect all pos traces we've ever seen. this will help us increase <maxNumPosTraces>
    	Set<AlloyTrace> allPosTracesSeen = Utils.setOf(initPosTrace);
    	
    	List<Formula> invariants = new ArrayList<>();
    	boolean formulaSeparates = false;
    	
    	int round = 1;
    	int cumNumPosTraces = 1; // cumulative number of pos traces seen so far
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
        	final AlloyTrace negTrace = genCexTraceForCandSepInvariant(tlaCompHV, cfgNegTraces, "NT", 1, "NegTrace", NEG_TRACE_TIMEOUT);
    		formulaSeparates = !negTrace.hasError();
    		System.out.println("attempting to eliminate the following neg trace this round:");
    		System.out.println(negTrace.fullSigString());

    		// reduce the max num pos traces in every round to "reset" them
    		for (final Map<String,String> evt : envVarTypes) {
    			final int max = maxNumPosTraces.get(evt);
    			final int numDuplicates = numDuplicateTracesPerRound.get(evt);
    			final int updatedMax = Math.max((max+numDuplicates)/2, INIT_MAX_POS_TRACES);
    			maxNumPosTraces.put(evt, updatedMax);
    			numDuplicateTracesPerRound.put(evt, 0); // reset this variable each round
    		}

    		// use the negative trace and all existing positive traces to generate a formula
			// keep generating positive traces until the formula turns into an invariant
    		boolean foundInvariant = false;
    		while (!formulaSeparates && !foundInvariant) {
				// trim <currentPosTraces> to be at most <maxNumPosTraces>
        		for (final Map<String,String> evt : envVarTypes) {
        			final int evtMaxNumPosTraces = maxNumPosTraces.get(evt);
        			List<AlloyTrace> evtCurrentPosTraces = currentPosTraces.get(evt);
    				while (evtCurrentPosTraces.size() > evtMaxNumPosTraces) {
    					evtCurrentPosTraces.remove(0);
    				}
    				//System.out.println("max # pos traces: " + evtMaxNumPosTraces);
        		}
				
				// synthesize new formulas
    			final int numFluents = this.useIntermediateProp ?
    					invariant.getNumFluents() + this.intermediateProp.getPastNumFluents() + 1 :
    					invariant.getNumFluents();
    			final Map<Map<String,String>, Formula> evtToFormulaMap = synthesizeFormulas(negTrace, currentPosTraces, numFluents, envVarTypes);
    			final Set<Formula> newSynthFormulas = evtToFormulaMap
    					.values()
    					.stream()
    					.filter(f -> !f.isUNSAT())
    					.collect(Collectors.toSet());
    			
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
    			
    			// if the latest constraints are unsatisfiable then stop and report this to the user
    			if (newSynthFormulas.isEmpty()) {
    				invariants.add(Formula.UNSAT());
    				return Formula.conjunction(invariants).getFormula();
    			}
    			
    			// generate positive traces to try and make the next set of formulas we synthesize invariants
    			final long fiveMinuteTimeout = 5L; // use a 5m timeout for pos traces
    			int ptNum = cumNumPosTraces;
    			Map<Formula, AlloyTrace> newSynthFormulaResults = new HashMap<>();
				for (final Formula formula : newSynthFormulas) {
					++ptNum;
					final String tlaRestHV = writeHistVarsSpec(tlaRest, cfgRest, formula, false);
					final AlloyTrace newPosTrace =
							genCexTraceForCandSepInvariant(tlaRestHV, cfgPosTraces, "PT", ptNum, "PosTrace", fiveMinuteTimeout);
					newSynthFormulaResults.put(formula, newPosTrace);
					
					// TODO hide this print behind a verbose flag
					final boolean isInvariant = !newPosTrace.hasError();
					System.out.println("Synthesized formula is invariant: " + isInvariant);
					System.out.println(formula);
				}
				System.out.println();
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
    			else {
            		for (final Map<String,String> evt : evtToFormulaMap.keySet()) {
            			final Formula newSynthFormula = evtToFormulaMap.get(evt);
            			final AlloyTrace newPosTrace = newSynthFormulaResults.get(newSynthFormula);
        				if (allPosTracesSeen.contains(newPosTrace)) {
        					final int origMax = maxNumPosTraces.get(evt);
        					final int origNumDuplicate = numDuplicateTracesPerRound.get(evt);
        					maxNumPosTraces.put(evt, origMax+1);
        					numDuplicateTracesPerRound.put(evt, origNumDuplicate+1);
        				}
    					Utils.assertTrue(!currentPosTraces.get(evt).contains(newPosTrace), "Synthesized a formula that doesn't respect a pos trace!");
            		}
            		
            		// gather the set of all new pos traces
            		final Set<AlloyTrace> allNewPosTraces = newSynthFormulaResults
							.values()
							.stream()
							.collect(Collectors.toSet());
            		
            		// print the cumulative set of new pos traces for the user
        			System.out.println();
        			System.out.println("new pos trace(s):");
        			allNewPosTraces
							.stream()
							.forEach(t -> System.out.println(t.fullSigString()));
    				
    				// notify the user that we've seen this trace at least once
        			final boolean tracesSeenBefore = allNewPosTraces
        					.stream()
        					.anyMatch(t -> allPosTracesSeen.contains(t));
    				if (tracesSeenBefore) {
    					System.out.println("(at least one trace has been seen before)");
    				}
    				
    				// keep track of all pos traces seen
    				cumNumPosTraces += ptNum;
					allPosTracesSeen.addAll(allNewPosTraces);
					
					// add the new pos trace to the set of current pos traces. if there is extra room at the end of
					// the pos trace list (i.e. the list is less than <maxNumPosTraces> per evt), then fill it with
					// pos traces found from other evt's. we make sure that we put the evt's own pos traces at the
					// end of the list so they remain in the list longer.
            		for (final Map<String,String> evt : evtToFormulaMap.keySet()) {
            			final int npt = currentPosTraces.get(evt).size() + 1;
            			final int max = maxNumPosTraces.get(evt);
            			final Formula evtFormula = evtToFormulaMap.get(evt);
            			final AlloyTrace newPosTrace = newSynthFormulaResults.get(evtFormula);
            			List<AlloyTrace> evtPosTraces = currentPosTraces.get(evt);
            			
            			// sanity check
            			Utils.assertTrue(!evtFormula.isUNSAT(), "UNSAT formula found in active env var types!");
            			
            			// add pos traces from other evt's to fill up to the max for this evt
            			if (npt < max) {
                			final Set<AlloyTrace> currentPosTraceSet = evtPosTraces.stream().collect(Collectors.toSet());
                			final Set<AlloyTrace> newPosTraceSet = Utils.setOf(newPosTrace);
                			final Set<AlloyTrace> evtPosTraceSet = Utils.union(currentPosTraceSet, newPosTraceSet);
                			List<AlloyTrace> additionalPosTraces = Utils.setMinus(allPosTracesSeen, evtPosTraceSet)
                					.stream()
                					.collect(Collectors.toList());
                			Collections.shuffle(additionalPosTraces);
                			
                			// trim <additionalPosTraces> to just the number of pos traces that will fit
                			final int numAdditionalTraces = Math.min(max - npt, additionalPosTraces.size());
                			while (additionalPosTraces.size() > numAdditionalTraces) {
                				additionalPosTraces.remove(additionalPosTraces.size()-1);
                			}
                			
                			// add the additional pos traces first so the trace <newPosTrace> will last longer
                			// in <evtPosTraces> (i.e. the traces in <additionalPosTraces> will be evicted from
                			// <evtPosTraces> earlier).
                			evtPosTraces.addAll(additionalPosTraces);
            			}
            			
            			// add the new pos trace
            			evtPosTraces.add(newPosTrace);
            		}
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
	
	/**
	 * This method creates a cex traces for the given spec (or an empty trace if no error is detected). This method is implemented in
	 * several steps:
	 * (1) Call out to TLC to find a cex trace
	 * (2) Parse the output of TLC to create a formula that helps reproduce the error
	 * (3) Using the formula from (2), create a new TLA+ spec that efficiently reproduces the error
	 * (4) Load the new TLA+ spec as a TLC object (i.e. in Java code) and get an action-based trace, which we turn into an AlloyTrace
	 * @param tla
	 * @param cfg
	 * @param trName
	 * @param trNum
	 * @param ext
	 * @return
	 */
	public AlloyTrace genCexTraceForCandSepInvariant(final String tla, final String cfg, final String trName, int trNum, final String ext, long timeout) {
		final String tlaName = tla.replaceAll("\\.tla", "");
		final String cfgName = cfg.replaceAll("\\.cfg", "");
		final String tlaFile = tlaName + ".tla";
		final String cfgFile = cfgName + ".cfg";
		final String cexTraceOutputFile = "cextrace.txt";
		
		// Step (1)
		// Call out to TLC to find a cex trace
		try {
			// TODO should use a temporary file for <cexTraceOutputFile>, right now there seems to be a race condition
			final String[] cmd = {"sh", "-c",
					"java -jar " + TLC_JAR_PATH + " -cleanup -deadlock -workers 12 -config " + cfgFile + " " + tlaFile + " > " + cexTraceOutputFile};
			Process proc = Runtime.getRuntime().exec(cmd);
			proc.waitFor(timeout, TimeUnit.MINUTES);
			
			// reached the timeout but TLC is still running--no error detected
			if (proc.isAlive()) {
				proc.destroyForcibly();
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
		
		
		// Step (2)
		// Parse the output of TLC to create a formula that helps reproduce the error
		
		// get the cex trace file, starting where the trace is
		final String cexTraceTxt = Utils.fileContents(cexTraceOutputFile)
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
		
		
		// Step (3)
		// Using the formula from (2), create a new TLA+ spec that efficiently reproduces the error
		
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
		
        
        // Step (4)
        // Load the new TLA+ spec as a TLC object (i.e. in Java code) and get an action-based trace, which we turn into an AlloyTrace
    	TLC tlcCexReproducer = new TLC();
    	tlcCexReproducer.modelCheck(cexTraceTla, cexTraceCfg);
    	final LTS<Integer, String> lts = tlcCexReproducer.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	Utils.assertTrue(!SafetyUtils.INSTANCE.ltsIsSafe(lts), "Couldn't reproduce TLC error!");
		
		// if candSep isn't an invariant, return a trace that should be covered by the formula
    	final int numTraces = 1; // only generate one trace at a time
    	final Set<List<String>> errTraces = MultiTraceCex.INSTANCE.findErrorTraces(lts, numTraces, this.tlcComp.actionsInSpec());
    	Set<AlloyTrace> cexs = new HashSet<>();
    	for (final List<String> errTrace : errTraces) {
    		final String name = trName + (trNum++);
    		cexs.add(createAlloyTrace(errTrace, name, ext));
    	}
		Utils.assertTrue(cexs.size() == 1, "expected one trace but there were " + cexs.size());
    	return Utils.chooseOne(cexs);
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
		return new AlloyTrace(trace, name, ext);
	}
	
	private Map<Map<String,String>, Formula> synthesizeFormulas(final AlloyTrace negTrace, final Map<Map<String,String>, List<AlloyTrace>> posTraces,
			final int curNumFluents, Set<Map<String,String>> envVarTypes) {
		FormulaSynth formSynth = new FormulaSynth(this.seed);
		return formSynth.synthesizeFormulas(envVarTypes, negTrace, posTraces,
				tlcComp, internalActions, sortElementsMap, setSortElementsMap, actionParamTypes, maxActParamLen,
				qvars, legalEnvVarCombos, curNumFluents);
	}
	
	private String writeHistVarsSpec(final String tla, final String cfg, final Formula candSep, boolean candSepInActions) {
    	final String tlaCompBaseName = tla.replaceAll("\\.tla", "");
    	final String specName = tlaCompBaseName + "_hist";
    	
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
	
	private static Map<String, Set<String>> createSortElementsMap(TLC tlc) {
		// create a map of sort -> elements (elements = atoms)
		Map<String, Set<String>> sortElements = new HashMap<>();
		for (final List<String> constList : tlc.tool.getModelConfig().getConstantsAsList()) {
			if (constList.size() == 2) {
				// constList is a CONSTANT assignment
				final String sort = constList.get(0);
				final Set<String> elems = parseElements(constList.get(1));
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
	private static Set<String> parseElements(final String rawSet) {
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
				.map(g -> sanitizeTokensForAlloy(g))
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
}

