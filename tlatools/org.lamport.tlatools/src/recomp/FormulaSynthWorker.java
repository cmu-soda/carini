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
	public static final String workerHeapSizeEnvVar = "FSYNTH_WORKER_HEAP_SIZE";
	
	// TODO make these params
	private static final int MAX_FORMULA_SIZE = 8; //7;
	private static final int MAX_NUM_FLUENT_ACTS = 5;
	
	private final FormulaSynth formulaSynth;
	private final Map<String,String> envVarTypes;
	private final int id;
	private final AlloyTrace negTrace;
	private final List<AlloyTrace> posTraces;
	private final TLC tlcSys;
	private final TLC tlcComp;
	private final Set<String> internalActions;
	private final Map<String, Set<String>> sortElementsMap;
	private final Map<String, List<String>> actionParamTypes;
	private final int maxActParamLen;
	private final Set<String> qvars;
	private final Set<Set<String>> legalEnvVarCombos;
	private final int curNumFluents;
	private final int numQuantifiers;

	// for some reason using a lock is much faster than using the synchronized keyword
	private final Lock lock;
	
	private Process process;
	private boolean globalTaskCompleted;

	public FormulaSynthWorker(FormulaSynth formulaSynth, Map<String,String> envVarTypes, int id,
			AlloyTrace negTrace, List<AlloyTrace> posTraces,
			TLC tlcSys, TLC tlcComp, Set<String> internalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, List<String>> actionParamTypes,
			int maxActParamLen, Set<String> qvars, Set<Set<String>> legalEnvVarCombos,
			int curNumFluents, int numQuantifiers) {
		this.formulaSynth = formulaSynth;
		this.envVarTypes = envVarTypes;
		this.id = id;
		this.negTrace = negTrace;
		this.posTraces = posTraces;
		this.tlcSys = tlcSys;
		this.tlcComp = tlcComp;
		this.internalActions = internalActions;
		this.sortElementsMap = sortElementsMap;
		this.actionParamTypes = actionParamTypes;
		this.maxActParamLen = maxActParamLen;
		this.qvars = qvars;
		this.legalEnvVarCombos = legalEnvVarCombos;
		this.curNumFluents = curNumFluents;
		this.numQuantifiers = numQuantifiers;
		
		this.lock = new ReentrantLock();
		this.process = null;
		this.globalTaskCompleted = false;
	}
	
	@Override
	public void run() {
		// TODO change name from "formula" to "json"
		PerfTimer timer = new PerfTimer();
		final String formula = synthesizeFormulaWithVarTypes(this.negTrace, this.posTraces);
		this.formulaSynth.setFormula(formula, this.id, timer.timeElapsedSeconds());
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
		final int formulaSize = MAX_FORMULA_SIZE + 1; // +1 because of the formula root
		final int numSymActs = MAX_NUM_FLUENT_ACTS;
		final String strFormulaSize = "for " + formulaSize + " Formula, " + numSymActs + " FlSymAction";
		
		// add all atoms, i.e. the values in each constant
		final Set<String> allAtoms = this.sortElementsMap.values()
				.stream()
				.reduce((Set<String>)new HashSet<String>(),
						(acc,s) -> Utils.union(acc, s),
						(s1,s2) -> Utils.union(s1,s2));
		final String strAtomList = String.join(", ", allAtoms);
		final String atomsDecl = "one sig " + strAtomList + " extends Atom {}";
		
		// define each sort as the set of its elements (elements = atoms)
		final String strSortDecls = this.sortElementsMap.keySet()
				.stream()
				.map(sort -> {
					final Set<String> elems = this.sortElementsMap.get(sort);
					final String atoms = String.join(" + ", elems);
					final String decl = "one sig " + sort + " extends Sort {} {\n"
							+ "	atoms = " + atoms + "\n"
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
		
		// determine the max length of the traces
		final Set<AlloyTrace> allTraces = Utils.union(posTraces.stream().collect(Collectors.toSet()), Utils.setOf(negTrace));
		final int maxTraceLen = allTraces.stream()
				.mapToInt(t -> t.lastIdx())
				.max()
				.getAsInt();
		
		// get a list of all the actions that occur across all traces; these are the only
		// actions we need to declare in the Alloy file
		final Set<String> allActions = allTraces
				.stream()
				.map(t -> t.trace().stream().collect(Collectors.toSet()))
				.reduce((Set<String>)new HashSet<String>(),
						(acc,s) -> Utils.union(acc, s),
						(s1,s2) -> Utils.union(s1, s2));
		
		// define each concrete action (and its base name) in the component
		Map<String,String> actToBaseName = new HashMap<>();
		StringBuilder concActsBuilder = new StringBuilder();
		for (final String act : this.tlcComp.actionsInSpec()) {
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
		
		// create the indices that are needed for the traces
		final String strIndices = IntStream.range(0, maxTraceLen+1)
				.mapToObj(i -> "T" + i)
				.collect(Collectors.joining(", "));
		final String strIndicesDecl = "one sig " + strIndices + " extends Idx {}";
		
		final String strIndicesNextMulti = IntStream.range(0, maxTraceLen)
				.mapToObj(i -> "T"+i + "->T"+(i+1))
				.collect(Collectors.joining(" + "));
		final String strIndicesNext = strIndicesNextMulti.isEmpty() ? "none->none" : strIndicesNextMulti;
		final String strInternalActs = this.internalActions
				.stream()
				.map(act -> "	no (Fluent.initFl + Fluent.termFl).baseName & " + act)
				.collect(Collectors.joining("\n"));
		final String strIndicesFacts = "fact {\n"
				+ "	IdxOrder/first = T0\n"
				+ "	IdxOrder/next = " + strIndicesNext + "\n"
				+ strInternalActs + "\n"
				+ "}";
		
		// declare facts about the variable types
		final String envVarForallFacts = this.envVarTypes.keySet()
				.stream()
				.map(v -> "	all f : Forall | (f.var = " + v + ") implies (f.sort = " + this.envVarTypes.get(v) + ")")
				.collect(Collectors.joining("\n"));
		final String envVarExistsFacts = this.envVarTypes.keySet()
				.stream()
				.map(v -> "	all f : Exists | (f.var = " + v + ") implies (f.sort = " + this.envVarTypes.get(v) + ")")
				.collect(Collectors.joining("\n"));
		final String envVarFacts = "fact {\n"
				+ envVarForallFacts + "\n"
				+ envVarExistsFacts + "\n"
				+ "}";
		
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
		// already been chosen yet.
		final String curNumFluentsComment = "//" + this.curNumFluents;
		
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
		final String lastIdxPartialInstance = "lastIdx = (EmptyTrace->T0) + " +
				allTraces.stream()
					.map(t -> "(" + t.name() + "->" + t.alloyLastIdx() + ")")
					.collect(Collectors.joining(" + "));
		final String pathPartialInstance = "path = " +
				allTraces.stream()
					.map(t -> "(" + t.name() + " -> " + t.path() + ")")
					.collect(Collectors.joining(" +\n		"));
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
					"	" + lastIdxPartialInstance + "\n\n" +
					"	" + pathPartialInstance + "\n\n" +
					"	" + strNonEmptyEnvsPartialInstance + "\n\n" +
					"	" + baseNamesPartialInstance + "\n" +
					"}";
		
		// number of quantifiers
		// numQuants=2 represents 1 and 2 quantifiers, while n (larger than 3) represents exactly n.
		// this is hacky, but works for now.
		final String quantFactsOp = this.numQuantifiers == 2 ? "<=" : "=";
		final String numQuantifiersFacts = "fact {\n"
				+ "	#(Forall + Exists) " + quantFactsOp + " " + this.numQuantifiers + "\n"
				+ "}";
		
		// pos trace delcs
		final List<String> posTraceDecls = posTraces
				.stream()
				.map(t -> t.toString())
				.collect(Collectors.toList());
		
		final String alloyFormulaInfer = curNumFluentsComment + "\n"
				+ baseAlloyFormulaInfer
				+ strFormulaSize + "\n"
				+ "\n" + paramIndicesDecl + "\n"
				+ "\n" + paramIndicesConstraints + "\n\n"
				+ "\n" + atomsDecl + "\n"
				+ "\n" + strSortDecls + "\n"
				+ "\n" + concActsBuilder.toString()
				+ "\n" + strIndicesDecl + "\n"
				+ "\n" + strIndicesFacts + "\n\n"
				//+ "\n" + envVarFacts + "\n\n" // overall, this makes things slower
				+ "\n" + envVarTypesFunc + "\n\n"
				+ "\n" + qvarDelc + "\n\n"
				+ "\n" + strNonEmptyEnvsDecls + "\n\n"
				+ "\n" + partialInstance + "\n\n"
				+ "\n" + numQuantifiersFacts + "\n\n"
				+ "\n" + negTrace + "\n\n"
				+ String.join("\n", posTraceDecls) + "\n";
		Utils.writeFile(fileName, alloyFormulaInfer);
	}

	private Set<Set<Utils.Pair<String,String>>> allEnvs(final Map<String,String> envVarTypes, final Set<String> atoms) {
		// don't include the empty env
		Set<Set<Utils.Pair<String,String>>> envs = allEnvs(envVarTypes, this.qvars, atoms, new HashSet<>());
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
	private static final String workerHeapSize = System.getenv(workerHeapSizeEnvVar) != null ? System.getenv(workerHeapSizeEnvVar) : "2G";
	private static final String alloyFormlaInferJar = alsmFormulaSynthesisPath + "/bin/alsm-formula-synthesis.jar";
	private static final String openWboLibPath = alsmFormulaSynthesisPath + "/lib/";
	
	private static final String baseAlloyFormulaInfer = "open util/boolean\n"
			+ "open util/ordering[Idx] as IdxOrder\n"
			+ "open util/ordering[ParamIdx] as ParamIdxOrder\n"
			+ "\n"
			+ "abstract sig Var {}\n"
			+ "\n"
			+ "abstract sig Atom {}\n"
			+ "\n"
			+ "abstract sig Sort {\n"
			+ "	atoms : some Atom\n"
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
			+ "/* Formula signatures (represented by a DAG) */\n"
			+ "abstract sig Formula {\n"
			+ "	children : set Formula\n"
			+ "}\n"
			+ "\n"
			+ "sig TT, FF extends Formula {} {\n"
			+ "	no children\n"
			+ "}\n"
			+ "\n"
			/*+ "sig Not extends Formula {\n"
			+ "	child : Formula\n"
			+ "} {\n"
			+ "	children = child\n"
			+ "}\n"*/
			+ "\n"
			+ "sig Implies extends Formula {\n"
			+ "	left : Formula,\n"
			+ "	right : Formula\n"
			+ "} {\n"
			+ "	children = left + right\n"
			+ "}\n"
			+ "\n"
			+ "sig FlSymAction {\n"
			+ "    baseName : BaseName,\n"
			+ "\n"
			+ "    // actToFlParamsMap maps action-params to fluent-params\n"
			+ "    // in other words, actToFlParamsMap decides which of the action-params will be\n"
			+ "    // used for setting a boolean value of the state variable (representing the\n"
			+ "    // fluent) in the _hist TLA+ code.\n"
			+ "    actToFlParamsMap : set(ParamIdx->ParamIdx)\n"
			+ "} {\n"
			+ "    // domain(actToFlParamsMap) \\subseteq paramIdxs(baseName)\n"
			+ "    actToFlParamsMap.ParamIdx in baseName.paramIdxs\n"
			+ "}\n"
			+ "\n"
			+ "sig Fluent extends Formula {\n"
			+ "    initially : Bool,\n"
			+ "    initFl : set FlSymAction,\n"
			+ "    termFl : set FlSymAction,\n"
			+ "\n"
			+ "    // vars represents the parameters (including the ordering) to the fluent itself\n"
			+ "	vars : set(ParamIdx->Var)\n"
			+ "} {\n"
			+ "    no children\n"
			//+ "    no initFl & termFl\n"
			+ "    no initFl.baseName & termFl.baseName // strong condition for ensuring initFl and termFl are mutex\n"
			+ "    some initFl + termFl\n"
			+ "    some vars\n"
			+ "\n"
			+ "    // vars is a function\n"
			+ "    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)\n"
			+ "\n"
			//+ "    // a base name can only occur once across all fluents\n"
			//+ "    all s1,s2 : (initFl + termFl) | (s1.baseName = s2.baseName) implies (s1 = s2)\n"
			+ "\n"
			+ "    // each fluent must accept all the fluent params in vars\n"
			+ "    all s : (initFl + termFl) | ParamIdx.(s.actToFlParamsMap) = vars.Var\n"
			+ "\n"
			+ "    // each action must input the same param-types to the fluent\n"
			+ "    let flParamTypes = vars.envVarTypes |\n"
			+ "        all a : (initFl+termFl) |\n"
			+ "            // for each param in the action, its type must match the fluent\n"
			+ "            all actIdx : a.actToFlParamsMap.ParamIdx |\n"
			+ "                let flIdx = actIdx.(a.actToFlParamsMap) |\n"
			+ "                    flIdx.flParamTypes = actIdx.(a.baseName.paramTypes)\n"
			+ "\n"
			+ "    // actToFlParamsMap is an injective function\n"
			+ "    // furthermore, when we combine actToFlParamsMap across all actions, the combination\n"
			+ "    // must STILL be injective\n"
			+ "    all x1,x2,y1,y2 : ParamIdx |\n"
			+ "        (x1->y1 in (initFl+termFl).actToFlParamsMap and x2->y2 in (initFl+termFl).actToFlParamsMap) implies (x1->y1 = x2->y2 or (not x1=x2 and not y1=y2))\n"
			+ "\n"
			+ "}\n"
			+ "\n"
			+ "sig Forall extends Formula {\n"
			+ "	var : Var,\n"
			+ "	sort : Sort,\n"
			+ "	matrix : Formula\n"
			+ "} {\n"
			+ "	children = matrix\n"
			+ "}\n"
			+ "\n"
			+ "sig Exists extends Formula {\n"
			+ "	var : Var,\n"
			+ "	sort : Sort,\n"
			+ "	matrix : Formula\n"
			+ "} {\n"
			+ "	children = matrix\n"
			+ "}\n"
			+ "\n"
			+ "one sig Root extends Formula {} {\n"
			+ "	one children\n"
			+ "}\n"
			+ "\n"
			+ "fact {\n"
			+ "	all f : Formula | f in Root.*children // all formulas must be a sub-formula of the root\n"
			+ "	no Root.^children & Root // root appears once\n"
			+ "	all f : Formula | f not in f.^children // eliminates cycles in formula nodes\n"
			+ "\n"
			+ "	ParamIdx.(Fluent.vars) in (Forall.var + Exists.var) // approximately: no free variables=\n"
			+ "\n"
			+ "	// do not quantify over a variable that's already in scope\n"
			+ "	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "\n"
			+ "	(Forall+Exists).^(~children) in (Root+Forall+Exists) // prenex normal form\n" // not clear whether this is efficient
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
			+ "abstract sig Idx {}\n"
			+ "\n"
			+ "abstract sig Trace {\n"
			+ "	path : Idx -> Act, // the path for the trace\n"
			+ "	lastIdx : Idx, // the last index in the path for the trace\n"
			+ "	satisfies : Env -> Idx -> Formula // formulas that satisfy this trace\n"
			+ "} {\n"
			+ "	// trace semantics, i.e. e |- t,i |= f, where e is an environment, t is a trace, i is an index, and f is a formula\n"
			+ "	all e : Env, i : Idx, f : TT | e->i->f in satisfies\n"
			+ "	all e : Env, i : Idx, f : FF | e->i->f not in satisfies\n"
			//+ "	all e : Env, i : Idx, f : Not | e->i->f in satisfies iff (e->i->f.child not in satisfies)\n"
			+ "	all e : Env, i : Idx, f : Implies | e->i->f in satisfies iff (e->i->f.left in satisfies implies e->i->f.right in satisfies)\n"
			//+ "	all e : Env, i : Idx, f : And | e->i->f in satisfies iff (e->i->f.left in satisfies and e->i->f.right in satisfies)\n"
			//+ "	all e : Env, i : Idx, f : Or | e->i->f in satisfies iff (e->i->f.left in satisfies or e->i->f.right in satisfies)\n"
			+ "\n"
			+ "    // e |- t,i |= f (where f is a fluent) iff any (the disjunction) of the following three hold:\n"
			+ "    // 1. i = 0 and f.initally = True and t[i] \\notin f.termFl\n"
			+ "    // 2. t[i] \\in f.initFl\n"
			+ "    // 3. t[i] \\notin f.termFl and (e |- t,i-1 |= f)\n"
			+ "	all e : Env, i : Idx, f : Fluent | e->i->f in satisfies iff\n"
			+ "        // a is the action at the current index i in the trace\n"
			+ "        let a = i.path |\n"
			+ "            ((i = IdxOrder/first and f.initially = True and not isTermAct[a,e,f]) or\n"
			+ "             (isInitAct[a,e,f]) or\n"
			+ "             (not isTermAct[a,e,f] and some i' : Idx | i'->i in IdxOrder/next and e->i'->f in satisfies))\n"
			+ "\n"
			+ "	all e : Env, i : Idx, f : Forall | e->i->f in satisfies iff\n"
			+ "		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)\n"
			+ "	all e : Env, i : Idx, f : Exists | e->i->f in satisfies iff\n"
			+ "		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)\n"
			+ "	all e : Env, i : Idx, f : Root | e->i->f in satisfies iff e->i->f.children in satisfies\n"
			+ "}\n"
			+ "\n"
			+ "// does this action initiate the fluent?\n"
			+ "pred isInitAct[a : Act, e : Env, f : Fluent] {\n"
			+ "    some s : f.initFl |\n"
			+ "        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps\n"
			+ "}\n"
			+ "\n"
			+ "// does this action terminate the fluent?\n"
			+ "pred isTermAct[a : Act, e : Env, f : Fluent] {\n"
			+ "    some s : f.termFl |\n"
			+ "        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps\n"
			+ "}\n"
			+ "\n"
			+ "pred pushEnv[env', env : Env, v : Var, x : Atom] {\n"
			+ "	env'.maps = env.maps + (v->x)\n"
			+ "}\n"
			+ "\n"
			+ "fun indices[t : Trace] : set Idx {\n"
			+ "	t.lastIdx.*(~IdxOrder/next)\n"
			+ "}\n"
			+ "\n"
			+ "fun rangeParamIdx[p : ParamIdx] : set ParamIdx {\n"
			+ "	p.*(~ParamIdxOrder/next)\n"
			+ "}\n"
			+ "\n"
			+ "abstract sig PosTrace extends Trace {} {}\n"
			+ "abstract sig NegTrace extends Trace {} {}\n"
			+ "one sig EmptyTrace extends Trace {} {\n"
			+ "	 no path\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "/* main */\n"
			+ "run {\n"
			+ "	// find a formula that separates \"good\" traces from \"bad\" ones\n"
			+ "	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies\n"
			+ "	all nt : NegTrace | no (EmptyEnv->nt.lastIdx->Root & nt.satisfies)\n"
			+ "	EmptyEnv->T0->Root in EmptyTrace.satisfies // the formula must satisfy the empty trace\n"
			+ "	minsome children // smallest formula possible\n"
			+ "	minsome initFl + termFl // heuristic to synthesize the least complicated fluents as possible\n"
			+ "}\n";
}
