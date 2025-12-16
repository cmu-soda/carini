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
	
	private final String tlaComp;
	private final String cfgComp;
	private final String tlaRest;
	private final String cfgRest;
	private final boolean useIntermediateProp;
	private final Formula intermediateProp;
	private final TLC tlcComp;
	private final TLC tlcRest;
	private final Set<String> allActions;
	private final Set<String> globalActions;
	private final Set<String> internalActions;
	private final Map<String, Set<String>> sortElementsMap;
	private final Map<String, Set<String>> rawSortElementsMap;
	private final Map<String, Map<String, Set<String>>> setSortElementsMap;
	private final Map<String, List<String>> actionParamTypes;
	private final int maxActParamLen;
	private final int maxNumVarsPerType;
	private final List<String> qvars;
	private final Set<Set<String>> legalEnvVarCombos;
	private final Set<Map<String,String>> allPermutations;
	private final boolean universal;
	private final int numWorkersPerBatch;
	private final int numSymActions;
	private final int formulaSize;
	private final long negTraceCheckMinutes;
	private final long posTraceCheckMinutes;
	private final String workerHeapSize;
	private final boolean extendedNegTraceSearch;
	private final Random seed;
	
	public FormulaSeparation(final String tlaComp, final String cfgComp, final String tlaRest, final String cfgRest, final String propFile,
			boolean universal, int numWorkers, int numSymActs, int formulaSize, int numQuants, long negTraceCheckMinutes, long posTraceCheckMinutes,
			String workerHeapSize, boolean extNegTraceSearch, long rseed) {
		this.tlaComp = tlaComp;
		this.cfgComp = cfgComp;
		this.tlaRest = tlaRest;
		this.cfgRest = cfgRest;
		
		tlcComp = new TLC();
    	tlcComp.initialize(tlaComp, cfgComp);
		tlcRest = new TLC();
    	tlcRest.initialize(tlaRest, cfgRest);
		
    	// the property file that's used for "intermediate" (i.e. fluent) properties
		this.useIntermediateProp = !propFile.equals("none");
		this.intermediateProp = this.useIntermediateProp ? new Formula( String.join("",Utils.fileContents(propFile)) ) : null;
		
    	// for convenience, also store the set of all actions
    	allActions = Utils.union(tlcComp.actionsInSpec(), tlcRest.actionsInSpec());
    	
		// the actions that are in the shared alphabet between comp and rest.
    	globalActions = Utils.intersection(tlcComp.actionsInSpec(), tlcRest.actionsInSpec());
    	
    	// the actions that are internal to either "comp" or "rest"
    	internalActions = Utils.setMinus(allActions, globalActions);
    	
    	// obtain a map of: sort -> Set(elements/atoms in the sort)
    	sortElementsMap = Utils.mergeMapsOrError(createSortElementsMap(tlcComp, true), createSortElementsMap(tlcRest, true)); // sanitized tokens
    	rawSortElementsMap = Utils.mergeMapsOrError(createSortElementsMap(tlcComp, false), createSortElementsMap(tlcRest, false)); // unsanitiszed tokens
    	
    	// obtain a map of: sort -> Set(elements/atoms in the sort) -> Set(elements/atoms in each set in the sort)
    	setSortElementsMap = Utils.mergeMapsOrError(createSetSortElementsMap(tlcComp), createSetSortElementsMap(tlcRest));
    	
    	// calculate all permutations of the sort elements
    	allPermutations = calcAllPermutations();
		
		// obtain a map of: action -> List(param type)
    	FastTool ftComp = (FastTool) tlcComp.tool;
    	FastTool ftRest = (FastTool) tlcRest.tool;
		actionParamTypes = Utils.mergeMapsOrError(
				TLC.getTransitionRelationNode(ftComp, tlcComp, "Next").actionParamTypes(tlcComp.actionsInSpec()),
				TLC.getTransitionRelationNode(ftRest, tlcRest, "Next").actionParamTypes(tlcRest.actionsInSpec()));
		maxActParamLen = actionParamTypes.values()
				.stream()
				.mapToInt(l -> l.size())
				.max()
				.getAsInt();

		maxNumVarsPerType = 3; // TODO make this a param
		final int maxNumVars = numQuants;
		final int numTypes = sortElementsMap.keySet().size();
		final int numVars = Math.min(maxNumVars, maxNumVarsPerType*numTypes);
		final String varNameBase = "var";
		qvars = IntStream.range(0, numVars)
				.mapToObj(i -> varNameBase + i)
				.collect(Collectors.toList());
		
		legalEnvVarCombos = IntStream.range(0, numVars)
				.mapToObj(i ->
					IntStream.range(0, i+1)
						.mapToObj(j -> varNameBase + j)
						.collect(Collectors.toSet()))
				.collect(Collectors.toSet());
		
		this.universal = universal;
		this.numWorkersPerBatch = numWorkers;
		this.numSymActions = numSymActs;
		this.formulaSize = formulaSize;
		this.negTraceCheckMinutes = negTraceCheckMinutes;
		this.posTraceCheckMinutes = posTraceCheckMinutes;
		this.workerHeapSize = workerHeapSize;
		this.extendedNegTraceSearch = extNegTraceSearch;
		this.seed = new Random(rseed);
	}
	
	public Formula synthesizeSepInvariant() {
		final Set<Formula> invariants = minimalSetOfSepInvariants();
    	
    	// write the _hist files with the entire invariant (for convenience for the user)
    	writeHistVarsSpec(tlaComp, cfgComp, Formula.conjunction(invariants), true);
    	writeHistVarsSpec(tlaRest, cfgRest, Formula.conjunction(invariants), false);
    	
    	// write out the formula to a file
    	final String tlaCompBaseName = this.tlaComp.replaceAll("\\.tla", "");
    	Utils.writeFile(tlaCompBaseName + ".inv", Formula.conjunction(invariants).toJson());
    	
    	return Formula.conjunction(invariants);
	}
	
	public Set<Formula> minimalSetOfSepInvariants() {
    	// config for producing negative traces
    	final String cfgNegTraces = "neg_traces.cfg";
    	final String cfgNegTracesContents = this.useIntermediateProp ?
    			cfgContentsWithoutInvariants(cfgComp) + "\nINVARIANT Safety" :
    			cfgContents(cfgComp);
    	Utils.writeFile(cfgNegTraces, cfgNegTracesContents);
    	
    	// config for producing positive traces
    	final String cfgPosTraces = "pos_traces.cfg";
		final String cfgPosTracesContents = cfgContentsWithoutInvariants(cfgRest) + "\nINVARIANT CandSep";
    	Utils.writeFile(cfgPosTraces, cfgPosTracesContents);
    	
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
    	
    	int largestFluentNumSeen = 0;
    	int numRoundsSinceBrandNewInvariant = 0;
    	Set<AlloyTrace> allNegTraces = new HashSet<>();
    	Map<Formula, Set<AlloyTrace>> invariantsToNegTracesBlocked = new HashMap<>();
    	Set<Formula> allInvariants = new HashSet<>();
    	Set<Formula> activeInvariants = new HashSet<>();
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
    		final Formula invariant = Formula.conjunction(activeInvariants);
        	final String tlaCompHV = writeHistVarsSpec(tlaComp, cfgComp, invariant, true);
			// the default timeout is 5m, but can be changed via env var
        	final AlloyTrace negTrace = genNegCexTraceForCandSepInvariant(tlaCompHV, cfgNegTraces, "NT", 1, "NegTrace", this.negTraceCheckMinutes);
    		formulaSeparates = !negTrace.hasError();
    		if (formulaSeparates) {
        		System.out.println("Round " + round + " took " + timer.timeElapsedSeconds() + " seconds");
    			System.out.println();
    			break;
    		}
    		System.out.println("attempting to eliminate the following neg trace this round:");
    		System.out.println(negTrace);
    		System.out.println();
    		Utils.assertTrue(!allNegTraces.contains(negTrace), "The neg trace has been seen before!");
    		
    		// whether or not we have found an invariant that blocks <negTrace>
    		boolean foundInvariant = false;
    		Formula blockingInvariant = null;
    		
    		// see if a backup invariant eliminates the neg trace
    		final Set<Formula> backupInvariants = Utils.setMinus(allInvariants, activeInvariants);
    		for (final Formula backupInv : backupInvariants) {
    			final boolean backupBlocksNegTrace = !isTraceInCompSpecWithFormula(negTrace, backupInv);
    			if (backupBlocksNegTrace) {
    				foundInvariant = true;
    				blockingInvariant = backupInv;
    				break;
    			}
    		}
    		
    		// calculate the min neg trace len needed for synthesizing an assumption. we will incrementally
    		// increase it as needed.
    		final int minPartialNegTraceLen = calculatePartialTraceLen(negTrace);
    		int partialNegTraceLen = minPartialNegTraceLen;
    		if (partialNegTraceLen == -1 && !formulaSeparates) {
        		// this means that the trace /is/ allowed by 'rest', and indicates an error in the spec
    			System.out.println("The property is violated with the following trace:");
    			System.out.println(negTrace);
    			return Utils.setOf(Formula.UNSAT());
    		}
        	
    		// keep track of pos traces corresponding to each env var type, as each env var type corresponds to a single
    		// formula synthesis task. these are the "current" pos traces that we will learn from (perform formula synth on).
        	long cumNumPosTraces = 1;
    		Map<Map<String,String>, List<AlloyTrace>> currentPosTraces = allEnvVarTypes
    				.stream()
    				.collect(Collectors.toMap(evt -> evt, evt -> new ArrayList<>()));

    		// use the negative trace and all existing positive traces to generate a formula
			// keep generating positive traces until the formula turns into an invariant
    		int numFormulaSynthBatches = 0;
    		while (!formulaSeparates && !foundInvariant) {
    			// compute the partial neg trace
    			final AlloyTrace partialNegTrace = negTrace.cutToLen(partialNegTraceLen);
    			System.out.println("Using the following partial neg trace for formula synth:");
        		System.out.println(partialNegTrace);
        		
				// synthesize new formulas
        		final int largestFluentNumInInvariants = allInvariants
        				.stream()
        				.reduce(0,
        						(n,inv) -> Math.max(n, inv.getMaxFluentNum()),
        						(n1,n2) -> Math.max(n1, n2));
        		final int largestFluentNumInAllFormulas = this.useIntermediateProp ?
    					Math.max(largestFluentNumInInvariants, this.intermediateProp.getMaxFluentNum()) :
    					largestFluentNumInInvariants;
        		largestFluentNumSeen = Math.max(largestFluentNumSeen, largestFluentNumInAllFormulas) + 1;
    			++numFormulaSynthBatches;
    			System.out.println("Formula synth batch: " + numFormulaSynthBatches);
    			final Map<Map<String,String>, Formula> evtToFormulaMap = synthesizeFormulas(partialNegTrace, currentPosTraces, largestFluentNumSeen, envVarTypes);
    			
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
    			
    			// if all results are UNSAT and we used a partial neg trace, then we increase the size of the partial neg trace
    			if (envVarTypes.isEmpty() && partialNegTraceLen < negTrace.size()) {
                    ++partialNegTraceLen;
    				numFormulaSynthBatches = 0;
                    envVarTypes = new HashSet<>(allEnvVarTypes);
                    currentPosTraces = allEnvVarTypes
            				.stream()
            				.collect(Collectors.toMap(evt -> evt, evt -> new ArrayList<>()));
                    System.out.println("All synthesized formulas are UNSAT, increasing the size of the partial neg trace");
                    System.out.println();
                    continue;
    			}
    			
    			// if all results are UNSAT (and in this case, we used the full length neg trace) then we report this to the user
    			if (envVarTypes.isEmpty()) {
    				// in this case, the overall constraints are unsatisfiable so we stop and report this to the user
    				activeInvariants.add(Formula.UNSAT());
    				return Utils.setOf(Formula.conjunction(activeInvariants));
    			}
    			
    			// generate positive traces to try and make the next set of formulas we synthesize invariants
    			Map<Formula, AlloyTrace> newSynthFormulaResults = new HashMap<>();
    			final List<Formula> sortedNewSynthFormulas = newSynthFormulas
    					.stream()
    					.sorted()
    					.collect(Collectors.toList());
				for (final Formula formula : sortedNewSynthFormulas) {
					// TODO hide this print behind a verbose flag
					System.out.println(formula);
					final String tlaRestHV = writeHistVarsSpec(tlaRest, cfgRest, formula, false);
					final AlloyTrace newPosTrace =
							genCexTraceForCandSepInvariant(tlaRestHV, cfgPosTraces, "PT", ++cumNumPosTraces, "PosTrace", this.posTraceCheckMinutes);
					newSynthFormulaResults.put(formula, newPosTrace);
					
					final boolean isInvariant = !newPosTrace.hasError();
					if (isInvariant) {
						blockingInvariant = formula;
						break;
					}
				}
				System.out.println();
				
				// update whether an invariant has been found
				foundInvariant = newSynthFormulaResults
    					.values()
    					.stream()
    					.anyMatch(t -> !t.hasError());
				
    			// if no new invariants have been found during formula synth, then prepare to perform formula synthesis
    			// with the new pos traces.
    			if (!foundInvariant) {
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
                			if (!intersectingTypeTraces.contains(evtTrace)) {
                				// this shouldn't happen. for now, print a warning and fix the problem, but it probably indicates a bug
                				// with sorts that share elements that should eventually be addressed properly.
                				intersectingTypeTraces.add(evtTrace); // so much for treating 'final' like 'const'
                				System.out.println("WARNING: evt: " + evt + " should contain the evtTrace: " + evtTrace);
                			}
                			//Utils.assertTrue(intersectingTypeTraces.contains(evtTrace), "evt: " + evt + " should contain the evtTrace: " + evtTrace);
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
							.forEach(t -> System.out.println(t));
        			System.out.println();
    			}
    		}
    		
    		// post processing after finding an invariant that blocks <negTrace>
    		
    		// print out the blocking invariant
    		final boolean brandNewInvariant = !allInvariants.contains(blockingInvariant);
    		if (brandNewInvariant) {
    			numRoundsSinceBrandNewInvariant = 0;
    			System.out.println("Found the following new invariant this round:");
    		} else {
    			++numRoundsSinceBrandNewInvariant;
    			System.out.println("The following previously found invariant blocks the negative trace:");
    		}
			System.out.println(blockingInvariant);
			System.out.println();

			// find the minimum set of invariants needed to block all neg traces seen so far
	    	System.out.println("Performing minimization book keeping.");
	    	PerfTimer minTimer = new PerfTimer();
	    	
	    	// if the new invariant hasn't been seen before, then update the <invariantsToNegTracesBlocked> map for all
	    	// past neg traces for the new invariant
    		if (!allInvariants.contains(blockingInvariant)) {
    			Utils.assertTrue(!invariantsToNegTracesBlocked.containsKey(blockingInvariant), "A previous invariant is in invariantsToNegTracesBlocked");
	    		invariantsToNegTracesBlocked.put(blockingInvariant, new HashSet<>());
	    		for (final AlloyTrace prevNegTrace : allNegTraces) {
	    			final boolean invBlocksPrevNegTrace = !isTraceInCompSpecWithFormula(prevNegTrace, blockingInvariant);
	    			if (invBlocksPrevNegTrace) {
        	    		invariantsToNegTracesBlocked.get(blockingInvariant).add(prevNegTrace);
	    			}
	    		}
    		}
    		
    		// update <invariantsToNegTracesBlocked> to record that the new invariant blocks the current neg trace
    		invariantsToNegTracesBlocked.get(blockingInvariant).add(negTrace);
	    	
	    	// update the <invariantsToNegTracesBlocked> map for the newest neg trace for all previous invariants
	    	for (final Formula inv : allInvariants) {
	    		if (!inv.equals(blockingInvariant)) {
		    		final boolean invBlocksNegTrace = !isTraceInCompSpecWithFormula(negTrace, inv);
	    			if (invBlocksNegTrace) {
	    	    		invariantsToNegTracesBlocked.get(inv).add(negTrace);
	    			}
	    		}
	    	}
			
	    	// update our data structures
			allInvariants.add(blockingInvariant);
    		allNegTraces.add(negTrace);
			System.out.println("Minimization book keeping finished in " + minTimer.timeElapsedSeconds() + " seconds");

			// only perform minimization at most twice in a row for previously found invariants
			final boolean minimize = numRoundsSinceBrandNewInvariant <= 2;
			if (minimize) {
		    	System.out.println("Minimizing the invariants found thus far.");
				activeInvariants = minimizeInvariants(allInvariants, invariantsToNegTracesBlocked, allNegTraces);
			} else {
		    	System.out.println("Not minimizing the invariants because it has been more than two rounds since a brand new invariant has been found.");
				activeInvariants.add(blockingInvariant);
			}
			
			System.out.println("Current partial assumption:\n" + Formula.conjunction(activeInvariants).getFormula());
    		System.out.println("Round " + round + " took " + timer.timeElapsedSeconds() + " seconds");
			System.out.println();
    		++round;
    		
    		// sanity check: the blocking invariant must be in the minimized formula if the invariant is brand new
    		// we don't perform this check if the formula isn't new because there may be multiple backup formulas that block
    		// the neg trace, and hence <blockingInvariant> may not appear in the minimized formula.
    		if (brandNewInvariant) {
    			Utils.assertTrue(activeInvariants.contains(blockingInvariant), "The new invariant was not included in the minimized formula");
    		}
    	}
    	
    	// the active invariants are a minimized set of invariants whose conjunction is a separating assumption
    	return activeInvariants;
	}
	
	private AlloyTrace createDefaultInitPosTrace() {
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
	
	private AlloyTrace createInitPosTrace(final String badAction, final AlloyTrace okNegPrefix, final AlloyTrace defaultInitPosTrace) {
    	final String badBaseAction = badAction.replaceAll("\\..*$", "");
    	final Set<String> okNegPrefixExtensions = new ExtendTraceVisitor<>(okNegPrefix.restrictToAlphabet(tlcRest.actionsInSpec()), globalActions)
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
    		return extendAlloyTrace(okNegPrefix, extAct, "PT1", "PosTrace");
    	}
    	// next best is to extend the trace with any next action
    	else if (!okNegPrefixExtensions.isEmpty()) {
    		final String extAct = Utils.chooseOne(okNegPrefixExtensions);
    		return extendAlloyTrace(okNegPrefix, extAct, "PT1", "PosTrace");
    	}
    	else if (!okNegPrefix.isEmpty()) {
    		return okNegPrefix;
    	}
    	return defaultInitPosTrace;
	}
	
	/**
	 * Returns the minimal set of invariants (from <invariantSet>) needed to block all traces in <allNegTraces>
	 * @param invariants
	 * @param invariantsToNegTracesBlocked
	 * @param allNegTraces
	 * @return
	 */
	public Set<Formula> minimizeInvariants(final Set<Formula> invariantSet, final Map<Formula, Set<AlloyTrace>> invariantsToNegTracesBlocked,
			final Set<AlloyTrace> allNegTraces) {
		List<Formula> invariants = invariantSet
				.stream()
				.collect(Collectors.toList());
		List<Formula> minInvariants = new ArrayList<>();
		Set<AlloyTrace> blockedNegTraces = new HashSet<>();
		while (!allNegTraces.equals(blockedNegTraces)) {
			Utils.assertTrue(!invariants.isEmpty(), "All invariants do not cover all neg traces");
			// sort the invariants based on how many neg traces they block
			Collections.sort(invariants, new Comparator<Formula>() {
				@Override
				public int compare(Formula f1, Formula f2) {
					// do not include previous blocked neg traces when comparing how many each formula blocks
					final Set<AlloyTrace> f1NegTracesBlocked =
							Utils.setMinus(invariantsToNegTracesBlocked.get(f1), blockedNegTraces);
					final Set<AlloyTrace> f2NegTracesBlocked =
							Utils.setMinus(invariantsToNegTracesBlocked.get(f2), blockedNegTraces);
					final int tracesBlockedComparison = f1NegTracesBlocked.size() - f2NegTracesBlocked.size();
					
					// if one formula blocks more traces, then choose it
					if (tracesBlockedComparison != 0) {
						return tracesBlockedComparison;
					}
					// otherwise (of both formulas block the same number of traces) then perform syntactic comparison
					return f1.compareTo(f2);
				}
			});
			// keep the invariant that blocks the most neg traces
			final int lastIdx = invariants.size() - 1;
			final Formula nextInv = invariants.remove(lastIdx);
			minInvariants.add(nextInv);
			blockedNegTraces.addAll(invariantsToNegTracesBlocked.get(nextInv));
		}
		return minInvariants
				.stream()
				.collect(Collectors.toSet());
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
		final List<String> tlcOutputLines = new NegTraceGen()
				.generate(tlaFile, cfgFile, detectError, extendedNegTraceSearch, timeout, TLC_JAR_PATH);
		System.out.println("TLC neg trace generation time: " + tlcTimer.timeElapsedSeconds() + " seconds");
		
		// make sure cextrace.txt has the most recent output for logging / auditing
		Utils.writeFile("cextrace.txt", String.join("\n", tlcOutputLines));
		
		// Parse the output of TLC to create a formula that helps reproduce the error
		
		// if there is no error then we're done
		final boolean noError = tlcOutputLines
				.stream()
				.allMatch(l -> !l.contains(detectError));
		if (noError) {
			return new AlloyTrace();
		}
		
		final int maxNumTotalTraces = 500; // TODO
		final int maxNumMinTraces = 100; // TODO
		final List<String> tlcErrorTraces = Utils.toArrayList(
				String.join("\n", tlcOutputLines).split(Pattern.quote(detectError)));
		final Set<AlloyTrace> alloyTraces = tlcErrorTraces
				.stream()
				.filter(t -> t.contains("State 1: <Initial predicate>"))
				.limit(maxNumTotalTraces)
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
				.collect(Collectors.toMap(t -> t, t -> calculatePartialTraceLen(t)));
		System.out.println("partial neg trace generation time: " + partialTraceLenTimer.timeElapsedSeconds() + " seconds");
		final int maxPartialTraceLen = minTraces
				.stream()
				.reduce(Integer.MIN_VALUE,
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
    	LTS<Integer, String> lts = tlcCexReproducer.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	if (SafetyUtils.INSTANCE.ltsIsSafe(lts)) {
    		// for some reason, this check is a bit flaky. if the LTS is safe, sleep for 1s and then try once more.
    		try {
				Thread.sleep(1000L);
			} catch (InterruptedException e) {}
        	tlcCexReproducer = new TLC();
        	tlcCexReproducer.modelCheck(cexTraceTla, cexTraceCfg);
        	lts = tlcCexReproducer.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	}
    	Utils.assertTrue(!SafetyUtils.INSTANCE.ltsIsSafe(lts), "Couldn't reproduce TLC error!");
		
		// if candSep isn't an invariant, return a trace that should be covered by the formula
    	final int numTraces = 1; // only generate one trace at a time
    	final Set<List<String>> errTraces = MultiTraceCex.INSTANCE.findErrorTraces(lts, numTraces, this.allActions);
		Utils.assertTrue(errTraces.size() == 1, "expected one err trace but there were " + errTraces.size());
		final List<String> errTrace = Utils.chooseOne(errTraces);
		final String name = trName + trNum;
		
		return createAlloyTrace(errTrace, name, ext);
	}
	
	/**
	 * calculate the minimal partial trace len, with respect to the "rest" spec
	 * @param trace
	 * @param tla
	 * @param cfg
	 * @return
	 */
	private int calculatePartialTraceLen(final AlloyTrace trace) {
		for (int i = 1; i <= trace.size(); ++i) {
			final AlloyTrace partialTrace = trace.cutToLen(i);
			final AlloyTrace restrictedPartialTrace = partialTrace.restrictToAlphabet(this.tlcRest.actionsInSpec());
			if (!restrictedPartialTrace.isEmpty()) {
				final boolean restSpecBlocksPartialTrace = !isTraceInSpec(restrictedPartialTrace, this.tlaRest, this.cfgRest, this.globalActions);
				if (restSpecBlocksPartialTrace) {
					return i;
				}
			}
		}
		return -1;
	}
	
	private boolean isTraceInCompSpecWithFormula(final AlloyTrace trace, final Formula formula) {
    	final String tlaCompHV = writeHistVarsSpec(tlaComp, cfgComp, formula, true);
    	return isTraceInSpec(trace, tlaCompHV, cfgComp, tlcComp.actionsInSpec());
	}
	
	private boolean isTraceInSpec(final AlloyTrace trace, final String tla, final String cfg, final Set<String> globalAlphabet) {
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
					final boolean isInternalAct = !globalAlphabet.contains(dname);
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
			if (retCode == 1) {
				// for some reason, every once in a while TLC returns a ret code of 1
				// TODO hide this behind a verbose mode
				System.out.println("Found ret code 1 from TLC, treating like ret code 12");
				return true;
			}
			Utils.assertTrue(retCode == 0 || retCode == 12, "isTraceInSpec(): unexpected ret code from TLC: " + retCode +
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
	
	private AlloyTrace createAlloyTrace(final List<String> rawTrace, final String name, final String ext) {
		final List<String> sanitizedTrace = rawTrace
				.stream()
				.map(a -> {
					return Utils.toArrayList(a.split("\\."))
							.stream()
							.map(p -> Utils.toArrayList(p.replaceAll("[{}]", "").split(","))) // conc act -> list of conc params
							.map(l -> sanitizeTokensForAlloy(l)) // sanitize each param so it can be encoded in an Alloy file
							.collect(Collectors.joining());
				})
				.collect(Collectors.toList());
		return new AlloyTrace(rawTrace, sanitizedTrace, name, ext, this.globalActions);
	}
	
	private AlloyTrace extendAlloyTrace(final AlloyTrace trace, final String extAct, final String name, final String ext) {
		List<String> newTrace = new ArrayList<>(trace.rawTrace());
		newTrace.add(extAct);
		return createAlloyTrace(newTrace, name, ext);
	}
	
	private Map<Map<String,String>, Formula> synthesizeFormulas(final AlloyTrace negTrace,
			final Map<Map<String,String>, List<AlloyTrace>> posTraces, final int curNumFluents, Set<Map<String,String>> envVarTypes) {
		final AlloyTrace globalNegTrace = negTrace.restrictToAlphabet(this.globalActions);
		final Map<Map<String,String>, List<AlloyTrace>> globalPosTraces = posTraces
				.keySet()
				.stream()
				.collect(Collectors.toMap(e -> e,
						e -> posTraces.get(e)
								.stream()
								.map(t -> t.restrictToAlphabet(this.globalActions))
								.collect(Collectors.toList())
						));
		FormulaSynth formSynth = new FormulaSynth(this.numWorkersPerBatch, this.seed);
		return formSynth.synthesizeFormulas(envVarTypes, globalNegTrace, globalPosTraces,
				tlcComp, globalActions, sortElementsMap, setSortElementsMap, actionParamTypes, maxActParamLen,
				qvars, legalEnvVarCombos, curNumFluents,
				universal, numSymActions, numSymActions, formulaSize, workerHeapSize);
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
		List<String> allQvars = this.qvars.stream().collect(Collectors.toList());
		Set<Map<String,String>> initEnvVarTypes = Utils.setOf(new HashMap<>());
		return createAllEnvVarTypes(allTypes, allQvars, initEnvVarTypes);
	}
	
	private Set<Map<String,String>> createAllEnvVarTypes(final Set<String> allTypes, List<String> remainingQvars,
			Set<Map<String,String>> partialEnvVarTypes) {
		if (remainingQvars.isEmpty()) {
			return partialEnvVarTypes;
		}

		Set<Map<String,String>> envVarTypes = new HashSet<>();
		final String qvar = remainingQvars.remove(0);
		for (final Map<String,String> origPartialEvt : partialEnvVarTypes) {
			for (final String type : allTypes) {
				Map<String,String> partialEvt = new HashMap<>(origPartialEvt);
				partialEvt.put(qvar, type);
				final boolean leqMaxNumVarsPerType = allTypes
						.stream()
						.map(t -> partialEvt.values().stream().filter(v -> v.equals(t)).count()) // number of vars per type
						.allMatch(c -> c <= this.maxNumVarsPerType);
				if (leqMaxNumVarsPerType) {
					envVarTypes.add(partialEvt);
				}
			}
		}
		return createAllEnvVarTypes(allTypes, remainingQvars, envVarTypes);
	}
	
	private static Map<String, Set<String>> createSortElementsMap(TLC tlc, boolean sanitize) {
		// create a map of sort -> elements (elements = atoms)
		Map<String, Set<String>> sortElements = new HashMap<>();
		for (final List<String> constList : tlc.tool.getModelConfig().getConstantsAsList()) {
			if (constList.size() == 2) {
				// constList is a CONSTANT assignment
				final String sort = constList.get(0);
				final Set<String> elems = parseElements(constList.get(1), sanitize);
				if (elems != null) {
					sortElements.put(sort, elems);
				}
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
        // Uncomment to allow (ignore) non-set constants
		//if (!(rawSetFirstChar == '{' && rawSetLastChar == '}')) {
			//return null;
		//}
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
	
	private static String cfgContents(final String cfg) {
		return Utils.fileContents(cfg)
				.stream()
				.collect(Collectors.joining("\n"));
	}
	
	private static String cfgContentsWithoutInvariants(final String cfg) {
		return Utils.fileContents(cfg)
				.stream()
				.filter(l -> !l.contains("INVARIANT "))
				.collect(Collectors.joining("\n"));
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
        // Uncomment to allow (ignore) non-set constants
		//if (!(rawSetFirstChar == '{' && rawSetLastChar == '}')) {
			//return null;
		//}
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

