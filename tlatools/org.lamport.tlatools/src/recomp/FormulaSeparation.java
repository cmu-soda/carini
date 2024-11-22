package recomp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.MultiTraceCex;
import cmu.isr.ts.lts.RandTraceUtils;
import cmu.isr.ts.lts.SafetyUtils;
import net.automatalib.words.Word;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.TLC;
import tlc2.Utils;
import tlc2.tool.impl.FastTool;

public class FormulaSeparation {
	private static final int INIT_MAX_POS_TRACES = 5;
	
	private final String tlaComp;
	private final String cfgComp;
	private final String tlaRest;
	private final String cfgRest;
	private final boolean useIntermediateProp;
	private final Formula intermediateProp;
	private final TLC tlcComp;
	private final TLC tlcRest;
	private final TLC tlcSys;
	private final Set<String> internalActions;
	private final Map<String, Set<String>> sortElementsMap;
	private final Map<String, List<String>> actionParamTypes;
	private final int maxActParamLen;
	private final int maxNumVarsPerType;
	private final Set<String> qvars;
	private final Set<Set<String>> legalEnvVarCombos;
	
	public FormulaSeparation(final String tlaComp, final String cfgComp, final String tlaRest, final String cfgRest,
			final String tlaSys, final String cfgSys, final String propFile) {
		this.tlaComp = tlaComp;
		this.cfgComp = cfgComp;
		this.tlaRest = tlaRest;
		this.cfgRest = cfgRest;
		
		this.useIntermediateProp = !propFile.equals("none");
		this.intermediateProp = this.useIntermediateProp ? new Formula( String.join("",Utils.fileContents(propFile)) ) : null;
		
		tlcComp = new TLC();
    	tlcComp.initialize(tlaComp, cfgComp);
		tlcSys = new TLC();
    	tlcSys.initialize(tlaSys, cfgSys);

    	System.out.println("Building the LTS for the initial trace (" + tlaSys + ")");
    	PerfTimer timer = new PerfTimer();
		tlcRest = new TLC();
    	tlcRest.modelCheck(tlaRest, cfgRest);
    	System.out.println("Built the LTS in " + timer.timeElapsedSeconds() + "s");
    	
    	// the actions that internal to "component"
    	internalActions = Utils.setMinus(tlcComp.actionsInSpec(), tlcRest.actionsInSpec());
    	
    	// obtain a map of: sort -> Set(elements/atoms in the sort)
    	sortElementsMap = createSortElementsMap(tlcSys);
		
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
    	
    	final AlloyTrace initPosTrace = createInitPosTrace();
    	
    	// the current pos traces that we will learn from (perform formula synth on)
    	List<AlloyTrace> currentPosTraces = new ArrayList<>();
    	currentPosTraces.add(initPosTrace);
    	
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
        	final AlloyTrace negTrace = genCexTraceForCandSepInvariant(tlaCompHV, cfgNegTraces, "NT", 1, "NegTrace");
    		formulaSeparates = !negTrace.hasError();
    		System.out.println("attempting to eliminate the following neg trace this round:");
    		System.out.println(negTrace.fullSigString());

    		// reset the max num pos traces in every round
        	int maxNumPosTraces = INIT_MAX_POS_TRACES; // the max num pos traces we'll allow during formula synthesis
			System.out.println("max # pos traces: " + maxNumPosTraces);
			
	    	// all (unique) pos traces that we've generated this round
	    	Set<AlloyTrace> allPosTracesSeen = new HashSet<>();
	    	allPosTracesSeen.addAll(currentPosTraces);

	    	// keeps track of the pos traces we've seen exactly once. we care about this because once a pos trace has
	    	// been seen twice, we will increment <maxNumPosTraces>. but we only want to increment <maxNumPosTraces> once
	    	// per a given pos trace, so we remove the pos trace from this set once we increment <maxNumPosTraces>.
	    	Set<AlloyTrace> posTracesSeenOnce = new HashSet<>();
	    	posTracesSeenOnce.addAll(currentPosTraces);

    		// use the negative trace and all existing positive traces to generate a formula
			// keep generating positive traces until the formula turns into an invariant
    		boolean isInvariant = false;
    		while (!formulaSeparates && !isInvariant) {
				// trim <currentPosTraces> to be at most <maxNumPosTraces>
				while (currentPosTraces.size() > maxNumPosTraces) {
					currentPosTraces.remove(0);
				}
				
				// synthesize a new formula
    			final int numFluents = this.useIntermediateProp ?
    					invariant.getNumFluents() + this.intermediateProp.getPastNumFluents() + 1 :
    					invariant.getNumFluents();
    			final Formula formula = synthesizeFormula(negTrace, currentPosTraces, numFluents, envVarTypes);
    			System.out.println("Synthesized: " + formula);
    			
    			// if the latest constraints are unsatisfiable then stop and report this to the user
    			if (formula.isUNSAT()) {
    				invariants.add(formula);
    				return Formula.conjunction(invariants).getFormula();
    			}
    			
    			// generate positive traces until the formula becomes an invariant
    			final int ptNum = cumNumPosTraces + 1;
    	    	final String tlaRestHV = writeHistVarsSpec(tlaRest, cfgRest, formula, false);
    			final AlloyTrace newPosTrace = genCexTraceForCandSepInvariant(tlaRestHV, cfgPosTraces, "PT", ptNum, "PosTrace");
    			isInvariant = !newPosTrace.hasError();
    			
    			if (isInvariant) {
    				invariants.add(formula);
    				System.out.println("The formula is an invariant! Moving to the next round.");
    			}
    			else {
        			System.out.println();
        			System.out.println("new pos trace:");
    				System.out.println(newPosTrace.fullSigString());
    				++cumNumPosTraces;
    				
    				// if we've seen this trace exactly once then increment <maxNumPosTraces>. also remove it from
    				// <posTracesSeenOnce>, since now we've seen it twice.
    				if (posTracesSeenOnce.contains(newPosTrace)) {
    					++maxNumPosTraces;
    					posTracesSeenOnce.remove(newPosTrace);
    				}
    				
    				// the case where <newPosTrace> is brand new, never seen before
    				if (!allPosTracesSeen.contains(newPosTrace)) {
    					Utils.assertTrue(!currentPosTraces.contains(newPosTrace), "Synthesized a formula that doesn't respect a pos trace!");
    					allPosTracesSeen.add(newPosTrace);
    					posTracesSeenOnce.add(newPosTrace);
    				}
    				else {
    					System.out.println("(trace has been seen before)");
    				}
    				
    				// add the new pos trace to the set of current pos traces
    				currentPosTraces.add(newPosTrace);
        			System.out.println("max # pos traces: " + maxNumPosTraces);
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
		System.out.println("Creating the initial trace");
		PerfTimer timer = new PerfTimer();
		
		// TODO make the init trace len a param
    	int initTraceLen = 4;
    	AlloyTrace initPosTrace = new AlloyTrace();
    	while (initPosTrace.isEmpty()) {
        	final List<String> initTrace =
        			RandTraceUtils.INSTANCE.randTrace(tlcRest.getLTSBuilder().toIncompleteDetAutWithoutAnErrorState(), initTraceLen)
        			.stream()
        			.collect(Collectors.toList());
        	initPosTrace = createAlloyTrace(initTrace, "PT1", "PosTrace");
        	++initTraceLen;
    	}
    	
    	System.out.println("Created the initial trace in " + timer.timeElapsedSeconds() + "s");
    	System.out.println();
    	return initPosTrace;
	}
	
	private AlloyTrace genCexTraceForCandSepInvariant(final String tla, final String cfg, final String trName, int trNum, final String ext) {
    	TLC tlc = new TLC();
    	tlc.modelCheck(tla, cfg);
    	final LTS<Integer, String> lts = tlc.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	
    	if (SafetyUtils.INSTANCE.ltsIsSafe(lts)) {
    		return new AlloyTrace();
    	}
		
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
	
	private Formula synthesizeFormula(final AlloyTrace negTrace, final List<AlloyTrace> posTraces, final int curNumFluents,
			final Set<Map<String,String>> envVarTypes) {
		FormulaSynth formSynth = new FormulaSynth();
		return formSynth.synthesizeFormula(envVarTypes, negTrace, posTraces,
				tlcComp, internalActions, sortElementsMap, actionParamTypes, maxActParamLen,
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
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals",
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
}

