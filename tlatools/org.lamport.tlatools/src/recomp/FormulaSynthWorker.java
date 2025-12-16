package recomp;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import tlc2.TLC;
import tlc2.Utils;

public class FormulaSynthWorker implements Runnable {
	public static final String alsmFormulaSynthEnvVar = "ALSM_FORMULA_SYNTH";
	private static final int MAX_FLUENT_ACT_PRIORITY = 2; // TODO make a param?
	
	private final FormulaSynth formulaSynth;
	private final Map<String,String> envVarTypes;
	private final int id;
	private final AlloyTrace negTrace;
	private final List<AlloyTrace> posTraces;
	private final int startNegIdx;
	private final TLC tlcComp;
	private final Set<String> globalActions;
	private final Map<String, Set<String>> sortElementsMap;
	private final Map<String, Map<String, Set<String>>> setSortElementsMap;
	private final Map<String, List<String>> actionParamTypes;
	private final int maxActParamLen;
	private final List<String> qvars;
	private final Set<Set<String>> legalEnvVarCombos;
	private final int curNumFluents;
	private final boolean universal;
	private final int numSymActions;
	private final int numTargets;
	private final int formulaSize;
	private final String workerHeapSize;

	// for some reason using a lock is much faster than using the synchronized keyword
	private final Lock lock;
	
	private Process process;
	private boolean globalTaskCompleted;

	public FormulaSynthWorker(FormulaSynth formulaSynth, Map<String,String> envVarTypes, int id,
			AlloyTrace negTrace, List<AlloyTrace> posTraces,
			TLC tlcComp, Set<String> globalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, Map<String, Set<String>>> setSortElementsMap,
			Map<String, List<String>> actionParamTypes,
			int maxActParamLen, List<String> qvars, Set<Set<String>> legalEnvVarCombos, int curNumFluents,
			boolean universal, int numSymActions, int numTargets, int formulaSize, String workerHeapSize) {
		this.formulaSynth = formulaSynth;
		this.envVarTypes = envVarTypes;
		this.id = id;
		this.negTrace = negTrace;
		this.startNegIdx = negTrace.size() - 1;
		this.posTraces = posTraces;
		this.tlcComp = tlcComp;
		this.globalActions = globalActions;
		this.sortElementsMap = sortElementsMap;
		this.setSortElementsMap = setSortElementsMap;
		this.actionParamTypes = actionParamTypes;
		this.maxActParamLen = maxActParamLen;
		this.qvars = qvars;
		this.legalEnvVarCombos = legalEnvVarCombos;
		this.curNumFluents = curNumFluents;
		this.universal = universal;
		this.numSymActions = numSymActions;
		this.numTargets = numTargets;
		this.formulaSize = formulaSize;
		this.workerHeapSize = workerHeapSize;
		
		this.lock = new ReentrantLock();
		this.process = null;
		this.globalTaskCompleted = false;
	}
	
	@Override
	public boolean equals(Object other) {
		if (!(other instanceof FormulaSynthWorker)) {
			return false;
		}
		final FormulaSynthWorker fswOther = (FormulaSynthWorker) other;
		return this.id == fswOther.id;
	}
	
	@Override
	public int hashCode() {
		return Integer.hashCode(this.id);
	}
	
	@Override
	public void run() {
		try {
			// TODO change name from "formula" to "json"
			PerfTimer timer = new PerfTimer();
			
			// check to make sure that no pos trace contains the neg trace, in which case the formula is
			// trivially UNSAT.
			final boolean isTriviallyUNSAT = this.posTraces
					.stream()
					.anyMatch(p -> p.contains(this.negTrace));
			if (isTriviallyUNSAT) {
				this.formulaSynth.setFormula("UNSAT", this.id, this.envVarTypes, timer.timeElapsedSeconds());
			}
			else {
				// call out to AlloyMax to synthesize a formula for us
				final String formula = synthesizeFormulaWithVarTypes(this.negTrace, this.posTraces);
				this.formulaSynth.setFormula(formula, this.id, this.envVarTypes, timer.timeElapsedSeconds());
			}
		} catch (RuntimeException e) {
			final String errFile = "worker" + this.id + "_err.log";
			final String errFileContents = e.toString() + "\n" + Utils.toArrayList(e.getStackTrace());
			Utils.writeFile(errFile, errFileContents);
		}
	}
	
	public void kill() {
		this.lock.lock();
		try {
			this.globalTaskCompleted = true;
			if (this.process != null && this.process.isAlive()) {
				// the alloy synthesis tool spawns child processes which may not be cleaned up by the parent
				killProcessAndAllChildren(this.process.toHandle());
			}
		}
		finally {
			this.lock.unlock();
		}
	}
	
	private static void killProcessAndAllChildren(ProcessHandle proc) {
		proc.children().forEach(p -> killProcessAndAllChildren(p));
		proc.destroyForcibly();
	}
	
	private Process createProcess(final String[] cmd) throws IOException {
		this.lock.lock();
		try {
			if (this.globalTaskCompleted) {
				return null;
			}
			else {
				return Runtime.getRuntime().exec(cmd);
			}
		}
		finally {
			this.lock.unlock();
		}
	}
	
	private String synthesizeFormulaWithVarTypes(final AlloyTrace negTrace, final List<AlloyTrace> posTraces) {
		final String alloyFormulaInferFile = "formula_infer_" + this.id + ".als";
		writeAlloyFormulaInferFile(alloyFormulaInferFile, negTrace, posTraces, this.envVarTypes);
		
		StringBuilder formulaBuilder = new StringBuilder();
		try {
			final String[] cmd = {"java", "-Xmx"+workerHeapSize, "-Djava.library.path=" + openWboLibPath, "-jar", alloyFormlaInferJar, "-f", alloyFormulaInferFile, "--tla", "--json"};
			this.process = createProcess(cmd);
			if (this.process == null) {
				// in this case, the worker has been killed so we simply return
				return "UNSAT";
			}
			BufferedReader reader = this.process.inputReader();
			String line = null;
			while ((line = reader.readLine()) != null) {
				formulaBuilder.append(line);
			}
			
			// to capture errors, we will need to put it into the json as an error field.
		}
		catch (Exception e) {
			// workers are expected to be killed if another completes first, no reason to report the exception
			// return UNSAT so the caller doesn't attempt to parse an incomplete / empty JSON formula
			return "UNSAT";
		}
		
		return formulaBuilder.toString();
	}
	
	private void writeAlloyFormulaInferFile(final String fileName, final AlloyTrace negTrace, final List<AlloyTrace> posTraces,
			final Map<String,String> envVarTypes) {
		final int formulaSize = this.formulaSize + 1; // +1 because of the formula root
		final int numSymActs = this.numSymActions;
		final int targetSize = this.numTargets;
		final String strFormulaSize = "for " + formulaSize + " Formula, " + numSymActs + " FlSymAction, " + targetSize + " Target";
		
		// define the setContains predicate
		final String rawContainsRelation = this.setSortElementsMap
				.values()
				.stream()
				.map(m -> {
					return m.keySet()
							.stream()
							.map(k -> {
								return m.get(k)
										.stream()
										.map(v -> k + "->" + v)
										.collect(Collectors.joining(" + "));
							})
							.collect(Collectors.joining(" + "));
				})
				.collect(Collectors.joining(" + "));
		final String containsRelation = rawContainsRelation.isEmpty() ? "none->none" : rawContainsRelation;
		final String setContainsPredicate = "pred setContains[s : Atom, e : Atom] {\n"
				+ "	let containsRel = (" + containsRelation + ") |\n"
				+ "		(s->e) in containsRel\n"
				+ "}";
		
		// predicate that encodes which sorts contain elements of other sorts. this is useful for VarSetContains.
		Map<String,String> isElemOfSetMap = new HashMap<>();
		for (final String elem : this.sortElementsMap.keySet()) {
			for (final String theSet : this.setSortElementsMap.keySet()) {
				final Set<String> elemElems = this.sortElementsMap.get(elem);
				final Set<String> theSetElems = this.setSortElementsMap.get(theSet)
						.values()
						.stream()
						.reduce((Set<String>)new HashSet<String>(),
								(acc,s) -> Utils.union(acc, s),
								(s1,s2) -> Utils.union(s1,s2));
				if (theSetElems.containsAll(elemElems)) {
					isElemOfSetMap.put(elem, theSet);
				}
			}
		}
		final String rawIsElemOfSetRelation = isElemOfSetMap
				.entrySet()
				.stream()
				.map(e -> e.getKey() + "->" + e.getValue())
				.collect(Collectors.joining(" + "));
		final String isElemOfSetRelation = rawIsElemOfSetRelation.isEmpty() ? "none->none" : rawIsElemOfSetRelation;
		final String isElemOfSetPred = "pred isElemOfSet[e : Sort, s : Sort] {\n"
				+ "	let elemOfRel = (" + isElemOfSetRelation + ") |\n"
				+ "		(e->s) in elemOfRel\n"
				+ "}";
		
		// add all atoms, i.e. the values in each constant
		final Set<String> allAtoms = this.sortElementsMap.values()
				.stream()
				.reduce((Set<String>)new HashSet<String>(),
						(acc,s) -> Utils.union(acc, s),
						(s1,s2) -> Utils.union(s1,s2));
		final String strAtomList = String.join(", ", allAtoms);
		final String atomsDecl = "one sig " + strAtomList + " extends Atom {}";
		
		// define the lte predicate
		final List<Integer> numbers = allAtoms
				.stream()
				.filter(a -> a.matches("NUM[0-9]+"))
				.map(n -> n.substring(3)) // remove NUM
				.map(n -> Integer.parseInt(n))
				.sorted() // not necessary, but makes the als file easier to read
				.collect(Collectors.toList());
		List<String> numericSortLte = new ArrayList<>();
		for (Integer i : numbers) {
			for (Integer j : numbers) {
				if (i <= j) {
					numericSortLte.add("NUM"+i + "->" + "NUM"+j);
				}
			}
		}
		final String rawLteRelation = String.join(" + ", numericSortLte);
		final String lteRelation = rawLteRelation.isEmpty() ? "none->none" : rawLteRelation;
		final String ltePredicate = "pred lte[lhs : Atom, rhs : Atom] {\n"
				+ "	let containsRel = (" + lteRelation + ") |\n"
				+ "		(lhs->rhs) in containsRel\n"
				+ "}";
		
		// define each sort as the set of its elements (elements = atoms)
		final String strSortDecls = this.sortElementsMap.keySet()
				.stream()
				.map(sort -> {
					final Set<String> elems = this.sortElementsMap.get(sort);
					final String atoms = String.join(" + ", elems);
					final boolean isNumericSort = elems
							.stream()
							.allMatch(e -> {
								// numeric types are of the form NUM<integer>
								if (e.length() <= 3) {
									return false;
								}
								try {
									Integer.parseInt(e.substring(3));
									return e.substring(0,3).equals("NUM");
								} catch (Exception ex) {}
								return false;
							});
					final String numericSort = isNumericSort ? "True" : "False";
					final String decl = "one sig " + sort + " extends Sort {} {\n"
							+ "	atoms = " + atoms + "\n"
							+ "	numericSort = " + numericSort + "\n"
							+ "}";
					return decl;
				})
				.collect(Collectors.joining("\n"));
		
		// define each param index
		final String strParamIndices = IntStream.range(0, maxActParamLen)
				.mapToObj(i -> "P" + i)
				.collect(Collectors.joining(", "));
		final String paramIndicesDecl = "one sig " + strParamIndices + " extends ParamIdx {}";
		
		// the params for each fluent must be ordered, i.e. P0, or P0 + P1, or P0 + P1 + P2, etc.
		final String fluentParamOpts = IntStream.range(0, maxActParamLen)
				.mapToObj(i -> {
					final String opts = IntStream.rangeClosed(0, i)
							.mapToObj(j -> "P"+j)
							.collect(Collectors.joining("+"));
					return "(f.vars.Var = " + opts + ")";
				})
				.collect(Collectors.joining(" or "));
		final String fluentParamOptsConstraint = "all f : Fluent | " + fluentParamOpts;
		
		// add constraints for param indices
		final String strNextMulti = IntStream.range(0, maxActParamLen-1)
				.mapToObj(i -> "P"+i + "->P"+(i+1))
				.collect(Collectors.joining(" + "));
		final String strNextDef = strNextMulti.isEmpty() ? "none->none" : strNextMulti;
		final String paramIndicesConstraints = "fact {\n"
				+ "	ParamIdxOrder/first = P0\n"
				+ "	ParamIdxOrder/next = " + strNextDef + "\n"
				+ "	" + fluentParamOptsConstraint + "\n"
				+ "}\n"
				+ "";
		
		// define each fluent priority index
		final String strFlActIndices = IntStream.range(0, MAX_FLUENT_ACT_PRIORITY)
				.mapToObj(i -> "S" + i)
				.collect(Collectors.joining(", "));
		final String fluentActPriorityDecl = "one sig " + strFlActIndices + " extends FlActionIdx {}";
		
		// add constraints for the fluent priority indices
		final String strNextMultiFluentPriority = IntStream.range(0, MAX_FLUENT_ACT_PRIORITY-1)
				.mapToObj(i -> "S"+i + "->S"+(i+1))
				.collect(Collectors.joining(" + "));
		final String strNextFluentPriorityDef = strNextMultiFluentPriority.isEmpty() ? "none->none" : strNextMultiFluentPriority;
		final String fluentActPriorityConstraints = "fact {\n"
				+ "	FlActionIdxOrder/first = S0\n"
				+ "	FlActionIdxOrder/next = " + strNextFluentPriorityDef + "\n"
				+ "}\n"
				+ "";
		
		// determine the max length of the traces
		List<AlloyTrace> allTraces = new ArrayList<>(posTraces);
		allTraces.add(negTrace);
		
		// get a list of all the actions that occur across all traces; these are the only
		// actions we need to declare in the Alloy file
		final Set<String> allActions = allTraces
				.stream()
				.map(t -> t.sanitizedTrace().stream().collect(Collectors.toSet()))
				.reduce((Set<String>)new HashSet<String>(),
						(acc,s) -> Utils.union(acc, s),
						(s1,s2) -> Utils.union(s1, s2));
		
		// define each concrete action (and its base name) in the component
		Map<String,String> actToBaseName = new HashMap<>();
		StringBuilder concActsBuilder = new StringBuilder();
		for (final String act : this.globalActions) {
			final List<String> paramTypes = this.actionParamTypes.get(act);
			final String paramIdxsDef = IntStream.range(0, paramTypes.size())
					.mapToObj(i -> "P" + i)
					.collect(Collectors.joining(" + "));
			final String paramIdxs = paramTypes.isEmpty() ? "no paramIdxs" : "paramIdxs = " + paramIdxsDef;
			final String paramTypesStr = IntStream.range(0, paramTypes.size())
					.mapToObj(i -> {
						final String idx = "P" + i;
						final String type = paramTypes.get(i);
						return idx + "->" + type;
					})
					.collect(Collectors.joining(" + "));
			final String strBaseDecl = "one sig " + act + " extends BaseName {} {\n"
					+ "	" + paramIdxs + "\n"
					+ "	paramTypes = " + paramTypesStr + "\n"
					+ "}";
			
			Set<List<String>> concreteActionParams = new HashSet<>();
			concreteActionParams.add(new ArrayList<>());
			for (final String paramType : paramTypes) {
				// type = sort
				Utils.assertTrue(this.sortElementsMap.containsKey(paramType), "sortElementsMap does not contain paramType: " + paramType);
				concreteActionParams = cartProduct(concreteActionParams, this.sortElementsMap.get(paramType));
			}
			
			final String strConcreteActions = concreteActionParams
					.stream()
					.filter(params -> {
						final String concActName = act + String.join("", params);
						return allActions.contains(concActName);
					})
					.map(params -> {
						final String concActName = act + String.join("", params);
						List<String> paramAssgs = new ArrayList<>();
						for (int i = 0; i < params.size(); ++i) {
							final String param = params.get(i);
							paramAssgs.add("P"+i + "->" + param);
						}
						final String strNonEmptyParams = "params = (" + String.join(" + ", paramAssgs) + ")";
						final String strParams = params.isEmpty() ? "no params" : strNonEmptyParams;
						actToBaseName.put(concActName, act);
						return "one sig " + concActName + " extends Act {} {\n"
								//+ "	baseName = " + act + "\n"
								+ "	" + strParams + "\n"
								+ "}";
					})
					.collect(Collectors.joining("\n"));
			
			concActsBuilder.append(strBaseDecl).append("\n").append(strConcreteActions).append("\n\n");
		}
		
		// meta function that encodes what type each var is. this is useful for the formula
		// synthesizer to recover the type of each variable when creating the json output.
		final String envVarTypesDef = this.envVarTypes.keySet()
				.stream()
				.map(v -> v + "->" + this.envVarTypes.get(v))
				.collect(Collectors.joining(" + "));
		final String envVarTypesFunc = "fun envVarTypes : set(Var->Sort) {\n"
				+ "	" + envVarTypesDef + "\n"
				+ "}";
		
		// meta comment that encodes the number of fluents that already exist. this is useful
		// for the formula synthesizer to rename each new fluent so it has a name that hasn't
		// already been chosen yet. we also include the worker id so each fluent in the batch
		// gets a unique name.
		final String curNumFluentsComment = "//" + this.curNumFluents;
		final String workerIdComment = "//" + this.id;
		
		// declare the quantifier variables
		final String qvarDelc = "one sig " + String.join(", ", this.qvars) + " extends Var {} {}";
		
		// create all possible environments such that:
		// 1. the environment is allowed by envVarTypes
		// 2. the environment obeys the var ordering specified in legalEnvVarCombos
		// envVars() ensures both of these constraints
		final String strNonEmptyEnvsDecls = allEnvs(envVarTypes, allAtoms)
				.stream()
				.map(env -> {
					final String name = env.stream().map(m -> m.first + "to" + m.second).collect(Collectors.joining());
					return "one sig " + name + " extends Env {} {}";
				})
				.collect(Collectors.joining("\n"));
		
		// partial instances for optimization
		final String strNonEmptyEnvsPartialInstance = "maps = " +
				allEnvs(envVarTypes, allAtoms)
				.stream()
				.map(env -> {
					final String name = env.stream().map(m -> m.first + "to" + m.second).collect(Collectors.joining());
					final String maps = env.stream().map(m -> m.first + "->" + m.second).collect(Collectors.joining(" + "));
					return name + "->(" + maps + ")";
					/*return "one sig " + name + " extends Env {} {\n"
						+ "	maps = " + maps + "\n"
						+ "}";*/
				})
				.collect(Collectors.joining(" +\n		"));
		final String baseNamesPartialInstance = "baseName = " +
				actToBaseName.keySet()
				.stream()
				.filter(a -> allActions.contains(a))
				.map(a -> a + "->" + actToBaseName.get(a))
				.collect(Collectors.joining(" +\n		"));
		final String partialInstance = "fact PartialInstance {\n" +
					"	" + strNonEmptyEnvsPartialInstance + "\n\n" +
					"	" + baseNamesPartialInstance + "\n" +
					"}";
		
		// restrict the number of quantifiers to the max num we allow
		// we also require that the first quantifier is a forall
		final String numQuantifiersFacts = "fact {\n"
				+ "	#(Forall + Exists) <= " + qvars.size() + " // allow only " + qvars.size() + " quantifiers\n"
				+ "	Root.children in Forall // the first quantifier must be a forall\n"
				+ "}";

		// disable Exists in universal mode
		final String universalFact = "fact {\n"
				+ "	no Exists // universal mode\n"
				+ "}";
		final String universalMode = this.universal ? ("\n" + universalFact + "\n") : "";
		
		final String stateDecls = createStateDecls(posTraces, negTrace, this.startNegIdx);
		
		// pos trace delcs
		final List<String> posTraceDecls = posTraces
				.stream()
				.map(t -> t.sigString())
				.collect(Collectors.toList());
		
		final String alloyFormulaInfer = curNumFluentsComment + "\n"
				+ workerIdComment + "\n"
				+ baseAlloyFormulaInfer
				+ strFormulaSize + "\n"
				+ "\n" + paramIndicesDecl + "\n"
				+ "\n" + paramIndicesConstraints + "\n\n"
				+ "\n" + fluentActPriorityDecl + "\n"
				+ "\n" + fluentActPriorityConstraints + "\n\n"
				+ "\n" + setContainsPredicate + "\n\n"
				+ "\n" + isElemOfSetPred + "\n\n"
				+ "\n" + ltePredicate + "\n\n"
				+ "\n" + atomsDecl + "\n"
				+ "\n" + strSortDecls + "\n"
				+ "\n" + concActsBuilder.toString()
				+ "\n" + envVarTypesFunc + "\n\n"
				+ "\n" + qvarDelc + "\n\n"
				+ "\n" + strNonEmptyEnvsDecls + "\n\n"
				+ "\n" + partialInstance + "\n\n"
				+ "\n" + numQuantifiersFacts + "\n\n"
				+ "\n" + stateDecls + "\n"
				+ universalMode;
		Utils.writeFile(fileName, alloyFormulaInfer);
	}
	
	private String createStateDecls(final List<AlloyTrace> posTraces, final AlloyTrace negTrace, int startNegIdx) {
		TraceTree traceTree = new TraceTree();
		for (final AlloyTrace tr : posTraces) {
			traceTree.addPosTrace(tr.sanitizedTrace());
		}
		traceTree.addNegTrace(negTrace.sanitizedTrace(), startNegIdx);
		return traceTree.toString();
	}

	private Set<Set<Utils.Pair<String,String>>> allEnvs(final Map<String,String> envVarTypes, final Set<String> atoms) {
		// don't include the empty env
		final Set<String> qvarSet = this.qvars.stream().collect(Collectors.toSet());
		Set<Set<Utils.Pair<String,String>>> envs = allEnvs(envVarTypes, qvarSet, atoms, new HashSet<>());
		envs.remove(new HashSet<>());
		return envs;
	}
	
	private Set<Set<Utils.Pair<String,String>>> allEnvs(final Map<String,String> envVarTypes, final Set<String> vars,
			final Set<String> atoms, Set<Utils.Pair<String,String>> env) {
		Set<Set<Utils.Pair<String,String>>> rv = new HashSet<>();
		
		// only compute "legal" var combos for the env. in practice this cuts down on redundant envs.
		// more specifically, we avoid computing multiple envs that are identical up to a variable renaming.
		final Set<String> envVars = env
				.stream()
				.map(p -> p.first)
				.collect(Collectors.toSet());
		if (this.legalEnvVarCombos.contains(envVars)) {
			rv.add(env);
		}
		
		// build all possible envs that are allowed by the envVarTypes typing map
		for (final String v : vars) {
			final String varType = envVarTypes.get(v);
			final Set<String> possibleAssignments = Utils.intersection(this.sortElementsMap.get(varType), atoms);
			for (final String a : possibleAssignments) {
				final Utils.Pair<String,String> newMap = new Utils.Pair<>(v, a);
				final Set<Set<Utils.Pair<String,String>>> envsFromNewMap =
						allEnvs(envVarTypes, Utils.setMinus(vars,Set.of(v)), atoms, Utils.union(env,Set.of(newMap)));
				final Set<Set<Utils.Pair<String,String>>> envsWithoutTheMap =
						allEnvs(envVarTypes, Utils.setMinus(vars,Set.of(v)), atoms, env);
				rv.addAll(envsFromNewMap);
				rv.addAll(envsWithoutTheMap);
			}
		}
		return rv;
	}
	
	
	/* Helper methods */
	
	private static Set<List<String>> cartProduct(final Set<List<String>> acc, final Set<String> s) {
		Set<List<String>> product = new HashSet<>();
		for (final List<String> acce : acc) {
			for (final String se : s) {
				List<String> l = new ArrayList<>(acce);
				l.add(se);
				product.add(l);
			}
		}
		return product;
	}
	
	private static final String alsmFormulaSynthesisPath = System.getenv(alsmFormulaSynthEnvVar);
	private static final String alloyFormlaInferJar = alsmFormulaSynthesisPath + "/bin/alsm-formula-synthesis.jar";
	private static final String openWboLibPath = alsmFormulaSynthesisPath + "/lib/";
	
	private static final String baseAlloyFormulaInfer = "open util/boolean\n"
			+ "open util/ordering[ParamIdx] as ParamIdxOrder\n"
			+ "open util/ordering[FlActionIdx] as FlActionIdxOrder\n"
			+ "\n"
			+ "abstract sig Var {}\n"
			+ "\n"
			+ "abstract sig Atom {}\n"
			+ "\n"
			+ "abstract sig Sort {\n"
			+ "	atoms : some Atom,\n"
			+ "	numericSort : Bool\n"
			+ "}\n"
			+ "\n"
			+ "abstract sig ParamIdx {}\n"
			+ "\n"
			+ "// base name for an action\n"
			+ "abstract sig BaseName {\n"
			+ "	paramIdxs : set ParamIdx,\n"
			+ "	paramTypes : set(ParamIdx->Sort)\n"
			+ "}\n"
			+ "\n"
			+ "// concrete action\n"
			+ "abstract sig Act {\n"
			+ "	baseName : BaseName,\n"
			+ "	params : ParamIdx->Atom\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "/* Target formula signatures */\n"
			+ "abstract sig Target {\n"
			+ "	tchildren : set Target\n"
			+ "}\n"
			+ "\n"
			+ "sig TT, FF extends Target {} {\n"
			+ "	no tchildren\n"
			+ "}\n"
			+ "\n"
			+ "sig NotTarget extends Target {\n"
			+ "	child : Target\n"
			+ "} {\n"
			+ "	tchildren = child\n"
			+ "	child in TT + FF // for now\n"
			+ "}\n"
			+ "\n"
			+ "// a Fluent within a target formula\n"
			+ "sig FluentTarget extends Target {\n"
			+ "    fluent : Fluent,\n"
			+ "    action : FlSymAction,\n"
			+ "    wrappingAction : FlSymAction,\n"
			+ "    flToActParamsMap : set(ParamIdx->ParamIdx)\n"
			+ "} {\n"
			+ "    no tchildren\n"
			+ "    fluent = action.fluent\n"
			+ "\n"
			+ "    // domain(flToActParamsMap) must be equal to the underlying fluent's domain\n"
			+ "    flToActParamsMap.ParamIdx = fluent.vars.Var\n"
			+ "\n"
			+ "    // range(flToActParamsMap) \\subseteq paramIdxs(baseName), i.e. the range must be valid param idxs\n"
			+ "    ParamIdx.flToActParamsMap in wrappingAction.baseName.paramIdxs\n"
			+ "\n"
			+ "    // flToActParamsMap is a function\n"
			+ "    all k,v1,v2 : ParamIdx | (k->v1 in flToActParamsMap and k->v2 in flToActParamsMap) implies (v1 = v2)\n"
			+ "\n"
			+ "    // flToActParamsMap is injective\n"
			+ "    // this is an overconstraint for improving speed\n"
			+ "    all k1,k2,v : ParamIdx | (k1->v in flToActParamsMap and k2->v in flToActParamsMap) implies (k1 = k2)\n"
			+ "\n"
			+ "    // the action must input the same param-types to the fluent\n"
			+ "    let flParamTypes = wrappingAction.fluent.vars.envVarTypes |\n"
			+ "    let inputTypes = flToActParamsMap.(action.baseName.paramTypes) |\n"
			+ "        flParamTypes = inputTypes\n"
			+ "}\n"
			+ "\n"
			+ "fact TargetConstraints {\n"
			+ "	all f : Target | f not in f.^tchildren // the DAG requirement\n"
			+ "	no FlSymAction.target.(~tchildren) // the target roots have no parents\n"
			+ "	Target = FlSymAction.target.*tchildren // all Targets must be part of a target formula\n"
			+ "\n"
			+ "    // specify the action that wraps each FluentTarget\n"
			+ "    all w : FluentTarget, s : FlSymAction | (w in s.target.*tchildren) implies (w.wrappingAction = s)\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "/* Formula signatures */\n"
			+ "abstract sig Formula {\n"
			+ "	children : set Formula\n"
			+ "}\n"
			+ "\n"
			+ "sig Not extends Formula {\n"
			+ "	child : Formula\n"
			+ "} {\n"
			+ "	children = child\n"
			+ "	child in (Fluent + VarEquals + VarSetContains + VarLTE)\n"
			+ "}\n"
			+ "\n"
			+ "sig Implies extends Formula {\n"
			+ "	left : Formula,\n"
			+ "	right : Formula\n"
			+ "} {\n"
			+ "	children = left + right\n"
			+ "	left != right\n"
			+ "	not (left in Not and right in Not) // for readability\n"
			+ "}\n"
			+ "\n"
			+ "abstract sig FlActionIdx {}\n"
			+ "\n"
			+ "sig FlSymAction {\n"
			+ "    baseName : BaseName,\n"
			+ "\n"
			+ "    // flToActParamsMap maps fluent-param idxs to action-param idxs.\n"
			+ "    // in other words, flToActParamsMap decides which of the action-params will be\n"
			+ "    // used for setting a boolean value of the state variable (representing the\n"
			+ "    // fluent) in the _hist TLA+ code.\n"
			+ "    flToActParamsMap : set(ParamIdx->ParamIdx),\n"
			+ "\n"
			+ "    // the target formula that describes how the action will perform its update\n"
			+ "    target : Target,\n"
			+ "\n"
			+ "    // the 'priority' of the action, which matters when there's multiple FlSymActions\n"
			+ "    // with the same base action.\n"
			+ "    flActIdx : FlActionIdx,\n"
			+ "\n"
			+ "    fluent : Fluent // the fluent this action is associated with\n"
			+ "} {\n"
			+ "    // domain(flToActParamsMap) must be a sequence of P0, P1, ... (i.e. no gaps between param numbers)\n"
			+ "    (no flToActParamsMap) or (P0 in flToActParamsMap.ParamIdx)\n"
			+ "    (flToActParamsMap.ParamIdx).*(~ParamIdxOrder/next) = flToActParamsMap.ParamIdx\n"
			+ "\n"
			+ "    // flToActParamsMap must have at most the number of variables in the fluent\n"
			+ "    flToActParamsMap.ParamIdx in fluent.vars.Var\n"
			+ "\n"
			+ "    // range(flToActParamsMap) \\subseteq paramIdxs(baseName), i.e. the range must be valid param idxs\n"
			+ "    ParamIdx.flToActParamsMap in baseName.paramIdxs\n"
			+ "\n"
			+ "    // flToActParamsMap is a function\n"
			+ "    all k,v1,v2 : ParamIdx | (k->v1 in flToActParamsMap and k->v2 in flToActParamsMap) implies (v1 = v2)\n"
			+ "\n"
			+ "    // flToActParamsMap is injective\n"
			+ "    // this is an overconstraint for improving speed\n"
			+ "    all k1,k2,v : ParamIdx | (k1->v in flToActParamsMap and k2->v in flToActParamsMap) implies (k1 = k2)\n"
			+ "\n"
			+ "    // it only makes sense for trueifies/falsifies to be the lowest priority action\n"
			+ "    (no flToActParamsMap) implies (flActIdx = S0)\n"
			+ "}\n"
			+ "\n"
			+ "sig Fluent extends Formula {\n"
			+ "    initially : Bool,\n"
			+ "    flActions : some FlSymAction,\n"
			+ "\n"
			+ "    // vars represents the parameters (including the ordering) to the fluent itself\n"
			+ "    vars : set(ParamIdx->Var)\n"
			+ "} {\n"
			+ "    no children\n"
			+ "    some vars\n"
			+ "\n"
			+ "    initially = False // makes the fluent easier to read, but doesn't sacrifice expressivity (because of Not)\n"
			+ "\n"
			+ "    // vars is a function\n"
			+ "    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)\n"
			+ "\n"
			+ "    // each action must input the same param-types to the fluent\n"
			+ "    let flParamTypes = vars.envVarTypes |\n"
			+ "        all a : flActions |\n"
			+ "            // for each param in the action, its type must match the fluent\n"
			+ "            let inputTypes = a.flToActParamsMap.(a.baseName.paramTypes) |\n"
			+ "                inputTypes in flParamTypes\n"
			+ "\n"
			+ "    // For each 'category' of FlSymAction's (the FlSymAction's that share the same base name), they must:\n"
			+ "    // 1. have different orderings (priorities) and\n"
			+ "    // 2. their orderings must form a sequence from 0 up to the max idx\n"
			+ "    all actName : BaseName |\n"
			+ "        let flActCategory = { a : flActions | a.baseName = actName } |\n"
			+ "        let maxIdx = FlActionIdxOrder/max[flActCategory.flActIdx] |\n"
			+ "            (all a1,a2 : flActCategory | (a1.flActIdx = a2.flActIdx implies a1=a2)) and\n"
			+ "            (flActCategory.flActIdx = rangeFlActionIdx[maxIdx])\n"
			+ "\n"
			+ "    // well-formedness constraint\n"
			+ "    all s : FlSymAction | (s in flActions) iff (s.fluent = this)\n"
			+ "}\n"
			+ "\n"
			+ "sig VarEquals extends Formula {\n"
			+ "    lhs : Var,\n"
			+ "    rhs : Var\n"
			+ "} {\n"
			+ "	no children\n"
			+ "	lhs != rhs\n"
			+ "	lhs.envVarTypes = rhs.envVarTypes // only compare vars of the same type\n"
			+ "}\n"
			+ "\n"
			+ "sig VarSetContains extends Formula {\n"
			+ "    elem : Var,\n"
			+ "    theSet : Var\n"
			+ "} {\n"
			+ "	no children\n"
			+ "	elem != theSet\n"
			+ "	isElemOfSet[elem.envVarTypes, theSet.envVarTypes]\n"
			+ "}\n"
			+ "\n"
			+ "sig VarLTE extends Formula {\n"
			+ "    sort : Sort,\n"
			+ "    lhs : Var,\n"
			+ "    rhs : Var\n"
			+ "} {\n"
			+ "	no children\n"
			+ "	lhs != rhs\n"
			+ "	lhs.envVarTypes = sort\n"
			+ "	rhs.envVarTypes = sort\n"
			+ "	sort.numericSort = True // the sort type must be numeric\n"
			+ "}\n"
			+ "\n"
			+ "sig Forall extends Formula {\n"
			+ "	var : Var,\n"
			+ "	sort : Sort,\n"
			+ "	matrix : Formula\n"
			+ "} {\n"
			+ "	children = matrix\n"
			+ "	sort = var.envVarTypes\n"
			+ "}\n"
			+ "\n"
			+ "sig Exists extends Formula {\n"
			+ "	var : Var,\n"
			+ "	sort : Sort,\n"
			+ "	matrix : Formula\n"
			+ "} {\n"
			+ "	children = matrix\n"
			+ "	sort = var.envVarTypes\n"
			+ "}\n"
			+ "\n"
			+ "one sig Root extends Formula {} {\n"
			+ "	one children\n"
			+ "}\n"
			+ "\n"
			+ "fact FormulaConstraints {\n"
			+ "	all f : Formula | f not in f.^children // the DAG requirement\n"
			+ "	no Root.(~children) // the root has no parents\n"
			+ "	all f : (Formula - Root) | one f.(~children) // all non-root formulas have exactly one parent\n"
			//+ "	Formula = Root.*children // all Formulas must be part of the overall formula\n"
			+ "\n"
			+ "	// no free vars, all vars must be used in the matrix\n"
			+ "	let varsInMatrix = ParamIdx.(Fluent.vars) + VarEquals.(lhs+rhs) + VarSetContains.(elem+theSet) + VarLTE.(lhs+rhs) |\n"
			+ "		varsInMatrix = (Forall.var + Exists.var)\n"
			+ "\n"
			+ "	// do not quantify over a variable that's already in scope\n"
			+ "	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "\n"
			+ "	(Forall+Exists).^(~children) in (Root+Forall+Exists) // prenex normal form\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "abstract sig Env {\n"
			+ "	maps : set(Var -> Atom)\n"
			+ "}\n"
			+ "one sig EmptyEnv extends Env {} {\n"
			+ "	no maps\n"
			+ "}\n"
			+ "\n"
			+ "abstract sig State {\n"
			+ "    prevState : lone State, // allows for trees made up of States, representing multiple traces\n"
			+ "    act : lone Act, // the action that led to this state\n"
			+ "    initiates : Env -> FlSymAction,\n"
			+ "    terminates : Env -> FlSymAction,\n"
			+ "    formulaSat : Env -> Formula,\n"
			+ "    targetSat : Target -> Act\n"
			+ "}\n"
			+ "\n"
			+ "fact TraceSemantics {\n"
			+ "    // Target formulas\n"
			+ "	all s : State, act : Act, f : TT | f->act in s.targetSat\n"
			+ "	all s : State, act : Act, f : FF | f->act not in s.targetSat\n"
			+ "	all s : State, act : Act, f : NotTarget | f->act in s.targetSat iff (f.child->act not in s.targetSat)\n"
			+ "	all s : State, act : Act, f : FluentTarget | f->act in s.targetSat iff\n"
			+ "        // a FluentTarget evaluates to true iff the fluent evaluates to true when passing in the concrete action\n"
			+ "        // args (via an environment) to the current value of the fluent.\n"
			+ "        let flEnv = { env : Env | (~(f.fluent.vars)).(f.flToActParamsMap).(act.params) = env.maps } |\n"
			+ "            some flEnv and flEnv->f.fluent in s.formulaSat\n"
			+ "\n"
			+ "\n"
			+ "    // fluent actions initiate iff their target formula evaluates to true (in the state before the action occurs)\n"
			+ "    all postState : State, e : Env, symAct : FlSymAction | e->symAct in postState.initiates iff\n"
			+ "        let a = postState.act |\n"
			+ "        let s = postState.prevState |\n"
			+ "        let isInitAct = concreteMatchesSymAction[e,a,symAct] and symAct.target->a in s.targetSat |\n"
			+ "        let isTermAct = concreteMatchesSymAction[e,a,symAct] and symAct.target->a not in s.targetSat |\n"
			+ "        let symActPrev = previousPriorityFlSymAction[symAct] |\n"
			+ "            some s and\n"
			+ "            (isInitAct or (not isTermAct and some symActPrev and e->symActPrev in postState.initiates))\n"
			+ "\n"
			+ "    // fluent actions terminate iff their target formula evaluates to false (in the state before the action occurs)\n"
			+ "    all postState : State, e : Env, symAct : FlSymAction | e->symAct in postState.terminates iff\n"
			+ "        let a = postState.act |\n"
			+ "        let s = postState.prevState |\n"
			+ "        let isInitAct = concreteMatchesSymAction[e,a,symAct] and symAct.target->a in s.targetSat |\n"
			+ "        let isTermAct = concreteMatchesSymAction[e,a,symAct] and symAct.target->a not in s.targetSat |\n"
			+ "        let symActPrev = previousPriorityFlSymAction[symAct] |\n"
			+ "            some s and\n"
			+ "            (isTermAct or (not isInitAct and some symActPrev and e->symActPrev in postState.terminates))\n"
			+ "\n"
			+ "\n"
			+ "	// state-based trace semantics\n"
			+ "	all s : State, e : Env, f : Not | e->f in s.formulaSat iff (e->f.child not in s.formulaSat)\n"
			+ "	all s : State, e : Env, f : Implies | e->f in s.formulaSat iff (e->f.left in s.formulaSat implies e->f.right in s.formulaSat)\n"
			+ "	all s : State, e : Env, f : VarEquals | e->f in s.formulaSat iff (f.lhs).(e.maps) = (f.rhs).(e.maps)\n"
			+ "	all s : State, e : Env, f : VarSetContains | e->f in s.formulaSat iff setContains[(f.theSet).(e.maps), (f.elem).(e.maps)]\n"
			+ "	all s : State, e : Env, f : VarLTE | e->f in s.formulaSat iff lte[(f.lhs).(e.maps), (f.rhs).(e.maps)]\n"
			+ "\n"
			+ "    all s : State, e : Env, f : Fluent | e->f in s.formulaSat iff\n"
			+ "        let a = s.act |\n"
			+ "        let symAct = highestPriorityFlSymAction[f,a] |\n"
			+ "        let isInitAct = some symAct and e->symAct in s.initiates |\n"
			+ "        let isTermAct = some symAct and e->symAct in s.terminates |\n"
			+ "            (no s.prevState and f.initially = True) or\n"
			+ "            (some s.prevState and isInitAct) or\n"
			+ "            (some s.prevState and not isTermAct and e->f in s.prevState.formulaSat)\n"
			+ "\n"
			+ "	all s : State, e : Env, f : Forall | e->f in s.formulaSat iff\n"
			+ "		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->f.matrix in s.formulaSat)\n"
			+ "	all s : State, e : Env, f : Exists | e->f in s.formulaSat iff\n"
			+ "		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->f.matrix in s.formulaSat)\n"
			+ "	all s : State, e : Env, f : Root | e->f in s.formulaSat iff e->f.children in s.formulaSat\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "pred concreteMatchesSymAction[e : Env, a : Act, s : FlSymAction] {\n"
			+ "    a.baseName = s.baseName and\n"
			+ "    (~(s.fluent.vars)).(s.flToActParamsMap).(a.params) in e.maps\n"
			+ "}\n"
			+ "\n"
			+ "fun highestPriority[cat : set FlSymAction] : FlActionIdx {\n"
			+ "    { s : cat | all s' : cat | FlActionIdxOrder/gte[s.flActIdx, s'.flActIdx] }.flActIdx\n"
			+ "}\n"
			+ "\n"
			+ "fun highestPriorityFlSymAction[f : Fluent, a : Act] : FlSymAction {\n"
			+ "    let flActCategory = { s : f.flActions | s.baseName = a.baseName } |\n"
			+ "    let si = highestPriority[flActCategory] |\n"
			+ "        { s : flActCategory | s.flActIdx = si }\n"
			+ "}\n"
			+ "\n"
			+ "fun previousPriorityFlSymAction[s : FlSymAction] : FlSymAction {\n"
			+ "    { sPrev : s.fluent.flActions | sPrev.flActIdx = s.flActIdx.prev }\n"
			+ "}\n"
			+ "\n"
			+ "pred pushEnv[env', env : Env, v : Var, x : Atom] {\n"
			+ "	env'.maps = env.maps + (v->x)\n"
			+ "}\n"
			+ "\n"
			+ "fun rangeParamIdx[p : ParamIdx] : set ParamIdx {\n"
			+ "	p.*(~ParamIdxOrder/next)\n"
			+ "}\n"
			+ "\n"
			+ "fun rangeFlActionIdx[s : FlActionIdx] : set FlActionIdx {\n"
			+ "	s.*(~FlActionIdxOrder/next)\n"
			+ "}\n"
			+ "\n"
			+ "abstract sig PosState extends State {}\n"
			+ "abstract sig NegState extends State {}\n"
			+ "\n"
			+ "\n"
			+ "// 'partial fluents' are fluents that do not update every param in the fluent (and hence, in practice,\n"
			+ "// update every sort value of the missing param).\n"
			+ "fun partialFluents : set FlSymAction {\n"
			+ "	 { a : FlSymAction | some f : Fluent | a in f.flActions and a.flToActParamsMap.ParamIdx != f.vars.Var }\n"
			+ "}\n"
			+ "\n"
			+ "// the violated neg states and all states that occur after. we want to maximize (i.e. maxsom) the number\n"
			+ "// of such states in order to minimize the index of the violation for the neg trace.\n"
			+ "fun violatedNegStatesAndAfter : set NegState {\n"
			+ "	 let violated = { s : NegState | EmptyEnv->Root not in s.formulaSat } |\n"
			+ "	 	 violated.*(~prevState)\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "/* main */\n"
			+ "run {\n"
			+ "	// find a formula that separates \"good\" traces from \"bad\" ones\n"
			+ "	// the requirement below only requies one neg state to be violated; this is ok because we assume there\n"
			+ "	// will be exactly one neg trace given.\n"
			+ "	all pt : PosState | EmptyEnv->Root in pt.formulaSat\n"
			+ "	some nt : NegState | EmptyEnv->Root not in nt.formulaSat\n"
			+ "\n"
			+ "	// minimization constraints\n"
			//+ "	maxsome violatedNegStatesAndAfter // minimize the violation idx (see above for why we use maxsome)\n" // this is not needed while using partial neg traces
			+ "	softno partialFluents // fewer partial fluents\n"
			+ "	softno (FlSymAction.target.*tchildren - (TT + FF)) // fewer targets that aren't TRUE or FALSE\n"
			+ "	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals\n"
			+ "	minsome flActions // heuristic to synthesize the least complicated fluents as possible\n"
			+ "	minsome Fluent.vars // minimize the # of params for each fluent\n"
			+ "}\n";
}
