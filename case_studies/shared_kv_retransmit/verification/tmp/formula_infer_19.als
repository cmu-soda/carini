//52
//19
open util/boolean
open util/ordering[ParamIdx] as ParamIdxOrder
open util/ordering[FlActionIdx] as FlActionIdxOrder

abstract sig Var {}

abstract sig Atom {}

abstract sig Sort {
	atoms : some Atom,
	numericSort : Bool
}

abstract sig ParamIdx {}

// base name for an action
abstract sig BaseName {
	paramIdxs : set ParamIdx,
	paramTypes : set(ParamIdx->Sort)
}

// concrete action
abstract sig Act {
	baseName : BaseName,
	params : ParamIdx->Atom
}


/* Target formula signatures */
abstract sig Target {
	tchildren : set Target
}

sig TT, FF extends Target {} {
	no tchildren
}

sig NotTarget extends Target {
	child : Target
} {
	tchildren = child
	child in TT + FF // for now
}

// a Fluent within a target formula
sig FluentTarget extends Target {
    fluent : Fluent,
    action : FlSymAction,
    wrappingAction : FlSymAction,
    flToActParamsMap : set(ParamIdx->ParamIdx)
} {
    no tchildren
    fluent = action.fluent

    // domain(flToActParamsMap) must be equal to the underlying fluent's domain
    flToActParamsMap.ParamIdx = fluent.vars.Var

    // range(flToActParamsMap) \subseteq paramIdxs(baseName), i.e. the range must be valid param idxs
    ParamIdx.flToActParamsMap in wrappingAction.baseName.paramIdxs

    // flToActParamsMap is a function
    all k,v1,v2 : ParamIdx | (k->v1 in flToActParamsMap and k->v2 in flToActParamsMap) implies (v1 = v2)

    // flToActParamsMap is injective
    // this is an overconstraint for improving speed
    all k1,k2,v : ParamIdx | (k1->v in flToActParamsMap and k2->v in flToActParamsMap) implies (k1 = k2)

    // the action must input the same param-types to the fluent
    let flParamTypes = wrappingAction.fluent.vars.envVarTypes |
    let inputTypes = flToActParamsMap.(action.baseName.paramTypes) |
        flParamTypes = inputTypes
}

fact TargetConstraints {
	all f : Target | f not in f.^tchildren // the DAG requirement
	no FlSymAction.target.(~tchildren) // the targets have no parents
	Target = FlSymAction.target.*tchildren // all Targets must be part of a target formula

    // specify the action that wraps each FluentTarget
    all w : FluentTarget, s : FlSymAction | (w in s.target.*tchildren) implies (w.wrappingAction = s)
}


/* Formula signatures */
abstract sig Formula {
	children : set Formula
}

sig Not extends Formula {
	child : Formula
} {
	children = child
	child in (Fluent + VarEquals + VarSetContains + VarLTE)
}

sig Implies extends Formula {
	left : Formula,
	right : Formula
} {
	children = left + right
	left != right
	not (left in Not and right in Not) // for readability
}

abstract sig FlActionIdx {}

sig FlSymAction {
    baseName : BaseName,

    // flToActParamsMap maps fluent-param idxs to action-param idxs.
    // in other words, flToActParamsMap decides which of the action-params will be
    // used for setting a boolean value of the state variable (representing the
    // fluent) in the _hist TLA+ code.
    flToActParamsMap : set(ParamIdx->ParamIdx),

    // the target formula that describes how the action will perform its update
    target : Target,

    // the 'priority' of the action, which matters when there's multiple FlSymActions
    // with the same base action.
    flActIdx : FlActionIdx,

    fluent : Fluent // the fluent this action is associated with
} {
    // domain(flToActParamsMap) must be a sequence of P0, P1, ... (i.e. no gaps between param numbers)
    (no flToActParamsMap) or (P0 in flToActParamsMap.ParamIdx)
    (flToActParamsMap.ParamIdx).*(~ParamIdxOrder/next) = flToActParamsMap.ParamIdx

    // flToActParamsMap must have at most the number of variables in the fluent
    flToActParamsMap.ParamIdx in fluent.vars.Var

    // range(flToActParamsMap) \subseteq paramIdxs(baseName), i.e. the range must be valid param idxs
    ParamIdx.flToActParamsMap in baseName.paramIdxs

    // flToActParamsMap is a function
    all k,v1,v2 : ParamIdx | (k->v1 in flToActParamsMap and k->v2 in flToActParamsMap) implies (v1 = v2)

    // flToActParamsMap is injective
    // this is an overconstraint for improving speed
    all k1,k2,v : ParamIdx | (k1->v in flToActParamsMap and k2->v in flToActParamsMap) implies (k1 = k2)

    // it only makes sense for trueifies/falsifies to be the lowest priority action
    (no flToActParamsMap) implies (flActIdx = S0)
}

sig Fluent extends Formula {
    initially : Bool,
    flActions : some FlSymAction,

    // vars represents the parameters (including the ordering) to the fluent itself
    vars : set(ParamIdx->Var)
} {
    no children
    some vars

    initially = False // makes the fluent easier to read, but doesn't sacrifice expressivity (because of Not)

    // vars is a function
    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)

    // each action must input the same param-types to the fluent
    let flParamTypes = vars.envVarTypes |
        all a : flActions |
            // for each param in the action, its type must match the fluent
            let inputTypes = a.flToActParamsMap.(a.baseName.paramTypes) |
                inputTypes in flParamTypes

    // For each 'category' of FlSymAction's (the FlSymAction's that share the same base name), they must:
    // 1. have different orderings (priorities) and
    // 2. their orderings must form a sequence from 0 up to the max idx
    all actName : BaseName |
        let flActCategory = { a : flActions | a.baseName = actName } |
        let maxIdx = FlActionIdxOrder/max[flActCategory.flActIdx] |
            (all a1,a2 : flActCategory | (a1.flActIdx = a2.flActIdx implies a1=a2)) and
            (flActCategory.flActIdx = rangeFlActionIdx[maxIdx])

    // well-formedness constraint
    all s : FlSymAction | (s in flActions) iff (s.fluent = this)
}

sig VarEquals extends Formula {
    lhs : Var,
    rhs : Var
} {
	no children
	lhs != rhs
	lhs.envVarTypes = rhs.envVarTypes // only compare vars of the same type
}

sig VarSetContains extends Formula {
    elem : Var,
    theSet : Var
} {
	no children
	elem != theSet
	isElemOfSet[elem.envVarTypes, theSet.envVarTypes]
}

sig VarLTE extends Formula {
    sort : Sort,
    lhs : Var,
    rhs : Var
} {
	no children
	lhs != rhs
	lhs.envVarTypes = sort
	rhs.envVarTypes = sort
	sort.numericSort = True // the sort type must be numeric
}

sig Forall extends Formula {
	var : Var,
	sort : Sort,
	matrix : Formula
} {
	children = matrix
}

sig Exists extends Formula {
	var : Var,
	sort : Sort,
	matrix : Formula
} {
	children = matrix
}

one sig Root extends Formula {} {
	one children
}

fact FormulaConstraints {
	all f : Formula | f not in f.^children // the DAG requirement
	no Root.(~children) // the root has no parents
	all f : (Formula - Root) | one f.(~children) // all non-root formulas have exactly one parent
	Formula = Root.*children // all Formulas must be part of the overall formula

	// no free vars, all vars must be used in the matrix
	let varsInMatrix = ParamIdx.(Fluent.vars) + VarEquals.(lhs+rhs) + VarSetContains.(elem+theSet) + VarLTE.(lhs+rhs) |
		varsInMatrix = (Forall.var + Exists.var)

	// do not quantify over a variable that's already in scope
	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)

	(Forall+Exists).^(~children) in (Root+Forall+Exists) // prenex normal form
}


abstract sig Env {
	maps : set(Var -> Atom)
}
one sig EmptyEnv extends Env {} {
	no maps
}

abstract sig State {
    prevState : lone State, // allows for trees made up of States, representing multiple traces
    act : lone Act, // the action that led to this state
    initiates : Env -> FlSymAction,
    terminates : Env -> FlSymAction,
    formulaSat : Env -> Formula,
    targetSat : Target -> Act
}

fact TraceSemantics {
    // Target formulas
	all s : State, act : Act, f : TT | f->act in s.targetSat
	all s : State, act : Act, f : FF | f->act not in s.targetSat
	all s : State, act : Act, f : NotTarget | f->act in s.targetSat iff (f.child->act not in s.targetSat)
	all s : State, act : Act, f : FluentTarget | f->act in s.targetSat iff
        // a FluentTarget evaluates to true iff the fluent evaluates to true when passing in the concrete action
        // args (via an environment) to the current value of the fluent.
        let flEnv = { env : Env | (~(f.fluent.vars)).(f.flToActParamsMap).(act.params) = env.maps } |
            some flEnv and flEnv->f.fluent in s.formulaSat


    // fluent actions initiate iff their target formula evaluates to true (in the state before the action occurs)
    all s : State, e : Env, a : FlSymAction | e->a in s.initiates iff
        let isInitAct = concreteMatchesSymAction[e,s.act,a] and a.target->s.act in s.prevState.targetSat |
        let isTermAct = concreteMatchesSymAction[e,s.act,a] and a.target->s.act not in s.prevState.targetSat |
        let aPrev = previousPriorityFlSymAction[a] |
            isInitAct
            or
            (not isTermAct and some aPrev and e->aPrev in s.initiates)

    // fluent actions terminate iff their target formula evaluates to false (in the state before the action occurs)
    all s : State, e : Env, a : FlSymAction | e->a in s.terminates iff
        let isInitAct = concreteMatchesSymAction[e,s.act,a] and a.target->s.act in s.prevState.targetSat |
        let isTermAct = concreteMatchesSymAction[e,s.act,a] and a.target->s.act not in s.prevState.targetSat |
        let aPrev = previousPriorityFlSymAction[a] |
            isTermAct
            or
            (not isInitAct and some aPrev and e->aPrev in s.terminates)


	// state-based trace semantics
	all s : State, e : Env, f : Not | e->f in s.formulaSat iff (e->f.child not in s.formulaSat)
	all s : State, e : Env, f : Implies | e->f in s.formulaSat iff (e->f.left in s.formulaSat implies e->f.right in s.formulaSat)
	all s : State, e : Env, f : VarEquals | e->f in s.formulaSat iff (f.lhs).(e.maps) = (f.rhs).(e.maps)
	all s : State, e : Env, f : VarSetContains | e->f in s.formulaSat iff setContains[(f.theSet).(e.maps), (f.elem).(e.maps)]
	all s : State, e : Env, f : VarLTE | e->f in s.formulaSat iff lte[(f.lhs).(e.maps), (f.rhs).(e.maps)]

    all s : State, e : Env, f : Fluent | e->f in s.formulaSat iff
        let a = highestPriorityFlSymAction[f,s.act] |
        let isInitAct = some a and concreteMatchesSymAction[e,s.act,a] and e->a in s.initiates |
        let isTermAct = some a and concreteMatchesSymAction[e,s.act,a] and e->a in s.terminates |
            (no s.prevState and f.initially = True) or
            (some s.prevState and isInitAct) or
            (some s.prevState and not isTermAct and e->f in s.prevState.formulaSat)

	all s : State, e : Env, f : Forall | e->f in s.formulaSat iff
		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->f.matrix in s.formulaSat)
	all s : State, e : Env, f : Exists | e->f in s.formulaSat iff
		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->f.matrix in s.formulaSat)
	all s : State, e : Env, f : Root | e->f in s.formulaSat iff e->f.children in s.formulaSat
}

pred concreteMatchesSymAction[e : Env, a : Act, s : FlSymAction] {
    a.baseName = s.baseName and
    (~(s.fluent.vars)).(s.flToActParamsMap).(a.params) in e.maps
}

fun highestPriority[cat : set FlSymAction] : FlActionIdx {
    { s : cat | all s' : cat | FlActionIdxOrder/gte[s.flActIdx, s'.flActIdx] }.flActIdx
}

fun highestPriorityFlSymAction[f : Fluent, a : Act] : FlSymAction {
    let flActCategory = { s : f.flActions | s.baseName = a.baseName } |
    let si = highestPriority[flActCategory] |
        { s : flActCategory | s.flActIdx = si }
}

fun previousPriorityFlSymAction[s : FlSymAction] : FlSymAction {
    { sPrev : s.fluent.flActions | sPrev.flActIdx = s.flActIdx.prev }
}

pred pushEnv[env', env : Env, v : Var, x : Atom] {
	env'.maps = env.maps + (v->x)
}

fun rangeParamIdx[p : ParamIdx] : set ParamIdx {
	p.*(~ParamIdxOrder/next)
}

fun rangeFlActionIdx[s : FlActionIdx] : set FlActionIdx {
	s.*(~FlActionIdxOrder/next)
}

abstract sig PosState extends State {}
abstract sig NegState extends State {}


// 'partial fluents' are fluents that do not update every param in the fluent (and hence, in practice,
// update every sort value of the missing param).
fun partialFluents : set FlSymAction {
	 { a : FlSymAction | some f : Fluent | a in f.flActions and a.flToActParamsMap.ParamIdx != f.vars.Var }
}

// the violated neg states and all states that occur after. we want to maximize (i.e. maxsom) the number
// of such states in order to minimize the index of the violation for the neg trace.
fun violatedNegStatesAndAfter : set NegState {
	 let violated = { s : NegState | EmptyEnv->Root not in s.formulaSat } |
	 	 violated.*(~prevState)
}


/* main */
run {
	// find a formula that separates "good" traces from "bad" ones
	// the requirement below only requies one neg state to be violated; this is ok because we assume there
	// will be exactly one neg trace given.
	all pt : PosState | EmptyEnv->Root in pt.formulaSat
	some nt : NegState | EmptyEnv->Root not in nt.formulaSat

	// minimization constraints
	maxsome violatedNegStatesAndAfter // minimize the violation idx (see above for why we use maxsome)
	softno partialFluents // fewer partial fluents
	softno (FlSymAction.target.*tchildren - (TT + FF)) // fewer targets that aren't TRUE or FALSE
	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals
	minsome flActions // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent.vars // minimize the # of params for each fluent
}
for 8 Formula, 4 FlSymAction, 4 Target

one sig P0, P1, P2, P3, P4 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = P0->P1 + P1->P2 + P2->P3 + P3->P4
	all f : Fluent | (f.vars.Var = P0) or (f.vars.Var = P0+P1) or (f.vars.Var = P0+P1+P2) or (f.vars.Var = P0+P1+P2+P3) or (f.vars.Var = P0+P1+P2+P3+P4)
}



one sig S0, S1 extends FlActionIdx {}

fact {
	FlActionIdxOrder/first = S0
	FlActionIdxOrder/next = S0->S1
}



pred setContains[s : Atom, e : Atom] {
	let containsRel = (none->none) |
		(s->e) in containsRel
}


pred isElemOfSet[e : Sort, s : Sort] {
	let elemOfRel = (none->none) |
		(e->s) in elemOfRel
}


pred lte[lhs : Atom, rhs : Atom] {
	let containsRel = (NUM1->NUM1 + NUM1->NUM2 + NUM2->NUM2) |
		(lhs->rhs) in containsRel
}


one sig n1, n2, k1, k2, NUM2, k3, v1, v2, NUM1 extends Atom {}

one sig Value extends Sort {} {
	atoms = v1 + v2
	numericSort = False
}
one sig Seqnum extends Sort {} {
	atoms = NUM2 + NUM1
	numericSort = True
}
one sig Key extends Sort {} {
	atoms = k1 + k2 + k3
	numericSort = False
}
one sig Node extends Sort {} {
	atoms = n1 + n2
	numericSort = False
}

one sig send_ack extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3 + P4
	paramTypes = P0->Node + P1->Node + P2->Key + P3->Value + P4->Seqnum
}


one sig reshard extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3 + P4
	paramTypes = P0->Node + P1->Node + P2->Key + P3->Value + P4->Seqnum
}
one sig reshardn1n1k1v1NUM1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->k1 + P3->v1 + P4->NUM1)
}
one sig reshardn1n1k1v1NUM2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->k1 + P3->v1 + P4->NUM2)
}
one sig reshardn1n1k2v1NUM1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->k2 + P3->v1 + P4->NUM1)
}
one sig reshardn1n1k2v1NUM2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->k2 + P3->v1 + P4->NUM2)
}
one sig reshardn2n2k2v1NUM1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->k2 + P3->v1 + P4->NUM1)
}
one sig reshardn2n2k1v1NUM1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->k1 + P3->v1 + P4->NUM1)
}
one sig reshardn1n1k1v2NUM1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->k1 + P3->v2 + P4->NUM1)
}
one sig reshardn1n2k1v1NUM1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->k1 + P3->v1 + P4->NUM1)
}
one sig reshardn2n1k1v1NUM1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->k1 + P3->v1 + P4->NUM1)
}
one sig reshardn2n1k1v1NUM2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->k1 + P3->v1 + P4->NUM2)
}
one sig reshardn2n2k1v2NUM1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->k1 + P3->v2 + P4->NUM1)
}

one sig retransmit extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3 + P4
	paramTypes = P0->Node + P1->Node + P2->Key + P3->Value + P4->Seqnum
}
one sig retransmitn1n1k1v1NUM1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->k1 + P3->v1 + P4->NUM1)
}
one sig retransmitn1n1k1v1NUM2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->k1 + P3->v1 + P4->NUM2)
}
one sig retransmitn1n2k1v1NUM1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->k1 + P3->v1 + P4->NUM1)
}
one sig retransmitn2n1k1v1NUM1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->k1 + P3->v1 + P4->NUM1)
}


fun envVarTypes : set(Var->Sort) {
	var2->Seqnum + var1->Key + var0->Seqnum
}


one sig var0, var1, var2 extends Var {} {}


one sig var1tok1var0toNUM1var2toNUM2 extends Env {} {}
one sig var1tok1var2toNUM1var0toNUM2 extends Env {} {}
one sig var1tok2var0toNUM1var2toNUM1 extends Env {} {}
one sig var1tok1var0toNUM1var2toNUM1 extends Env {} {}
one sig var0toNUM1 extends Env {} {}
one sig var1tok1var0toNUM2 extends Env {} {}
one sig var1tok2var0toNUM1 extends Env {} {}
one sig var1tok1var0toNUM1 extends Env {} {}
one sig var0toNUM2 extends Env {} {}
one sig var0toNUM2var1tok3var2toNUM2 extends Env {} {}
one sig var0toNUM2var1tok3 extends Env {} {}
one sig var1tok2var0toNUM2var2toNUM2 extends Env {} {}
one sig var0toNUM1var1tok3var2toNUM2 extends Env {} {}
one sig var2toNUM1var0toNUM2var1tok3 extends Env {} {}
one sig var1tok2var0toNUM2 extends Env {} {}
one sig var0toNUM1var1tok3 extends Env {} {}
one sig var1tok1var0toNUM2var2toNUM2 extends Env {} {}
one sig var1tok2var0toNUM1var2toNUM2 extends Env {} {}
one sig var1tok2var2toNUM1var0toNUM2 extends Env {} {}
one sig var0toNUM1var2toNUM1var1tok3 extends Env {} {}


fact PartialInstance {
	maps = var1tok1var0toNUM1var2toNUM2->(var1->k1 + var0->NUM1 + var2->NUM2) +
		var1tok1var2toNUM1var0toNUM2->(var1->k1 + var2->NUM1 + var0->NUM2) +
		var1tok2var0toNUM1var2toNUM1->(var1->k2 + var0->NUM1 + var2->NUM1) +
		var1tok1var0toNUM1var2toNUM1->(var1->k1 + var0->NUM1 + var2->NUM1) +
		var0toNUM1->(var0->NUM1) +
		var1tok1var0toNUM2->(var1->k1 + var0->NUM2) +
		var1tok2var0toNUM1->(var1->k2 + var0->NUM1) +
		var1tok1var0toNUM1->(var1->k1 + var0->NUM1) +
		var0toNUM2->(var0->NUM2) +
		var0toNUM2var1tok3var2toNUM2->(var0->NUM2 + var1->k3 + var2->NUM2) +
		var0toNUM2var1tok3->(var0->NUM2 + var1->k3) +
		var1tok2var0toNUM2var2toNUM2->(var1->k2 + var0->NUM2 + var2->NUM2) +
		var0toNUM1var1tok3var2toNUM2->(var0->NUM1 + var1->k3 + var2->NUM2) +
		var2toNUM1var0toNUM2var1tok3->(var2->NUM1 + var0->NUM2 + var1->k3) +
		var1tok2var0toNUM2->(var1->k2 + var0->NUM2) +
		var0toNUM1var1tok3->(var0->NUM1 + var1->k3) +
		var1tok1var0toNUM2var2toNUM2->(var1->k1 + var0->NUM2 + var2->NUM2) +
		var1tok2var0toNUM1var2toNUM2->(var1->k2 + var0->NUM1 + var2->NUM2) +
		var1tok2var2toNUM1var0toNUM2->(var1->k2 + var2->NUM1 + var0->NUM2) +
		var0toNUM1var2toNUM1var1tok3->(var0->NUM1 + var2->NUM1 + var1->k3)

	baseName = reshardn1n1k2v1NUM2->reshard +
		reshardn2n1k1v1NUM1->reshard +
		reshardn1n1k2v1NUM1->reshard +
		reshardn2n1k1v1NUM2->reshard +
		reshardn1n2k1v1NUM1->reshard +
		reshardn1n1k1v1NUM1->reshard +
		retransmitn2n1k1v1NUM1->retransmit +
		reshardn1n1k1v1NUM2->reshard +
		retransmitn1n2k1v1NUM1->retransmit +
		reshardn2n2k2v1NUM1->reshard +
		reshardn2n2k1v2NUM1->reshard +
		retransmitn1n1k1v1NUM1->retransmit +
		reshardn1n1k1v2NUM1->reshard +
		retransmitn1n1k1v1NUM2->retransmit +
		reshardn2n2k1v1NUM1->reshard
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig PosState1 extends PosState {} {
    no prevState
    no act
}

one sig PosState5 extends PosState {} {
    prevState = PosState1
    act = reshardn2n1k1v1NUM1
}

one sig PosState6 extends PosState {} {
    prevState = PosState5
    act = retransmitn2n1k1v1NUM1
}

one sig PosState2 extends PosState {} {
    prevState = PosState1
    act = reshardn1n1k1v1NUM1
}

one sig PosState3 extends PosState {} {
    prevState = PosState2
    act = reshardn2n1k1v1NUM1
}

one sig PosState4 extends PosState {} {
    prevState = PosState3
    act = retransmitn2n1k1v1NUM1
}

one sig PosState36 extends PosState {} {
    prevState = PosState3
    act = retransmitn1n1k1v1NUM1
}

one sig PosState49 extends PosState {} {
    prevState = PosState2
    act = reshardn1n1k2v1NUM2
}

one sig PosState50 extends PosState {} {
    prevState = PosState49
    act = reshardn2n1k1v1NUM2
}

one sig NegState51 extends NegState {} {
    prevState = PosState50
    act = retransmitn1n1k1v1NUM2
}

one sig PosState44 extends PosState {} {
    prevState = PosState2
    act = reshardn1n1k2v1NUM1
}

one sig PosState45 extends PosState {} {
    prevState = PosState44
    act = retransmitn1n1k1v1NUM1
}

one sig PosState22 extends PosState {} {
    prevState = PosState2
    act = reshardn1n2k1v1NUM1
}

one sig PosState28 extends PosState {} {
    prevState = PosState22
    act = retransmitn1n2k1v1NUM1
}

one sig PosState18 extends PosState {} {
    prevState = PosState2
    act = reshardn1n1k1v1NUM1
}

one sig PosState23 extends PosState {} {
    prevState = PosState18
    act = reshardn2n1k1v1NUM1
}

one sig PosState38 extends PosState {} {
    prevState = PosState23
    act = retransmitn2n1k1v1NUM1
}

one sig PosState24 extends PosState {} {
    prevState = PosState23
    act = retransmitn1n1k1v1NUM1
}

one sig PosState19 extends PosState {} {
    prevState = PosState18
    act = retransmitn1n1k1v1NUM1
}

one sig PosState20 extends PosState {} {
    prevState = PosState19
    act = reshardn2n1k1v1NUM1
}

one sig PosState25 extends PosState {} {
    prevState = PosState19
    act = reshardn1n1k2v1NUM1
}

one sig PosState48 extends PosState {} {
    prevState = PosState19
    act = reshardn1n1k1v1NUM2
}

one sig PosState7 extends PosState {} {
    prevState = PosState2
    act = retransmitn1n1k1v1NUM1
}

one sig PosState42 extends PosState {} {
    prevState = PosState7
    act = reshardn2n1k1v1NUM1
}

one sig PosState46 extends PosState {} {
    prevState = PosState42
    act = retransmitn2n1k1v1NUM1
}

one sig PosState43 extends PosState {} {
    prevState = PosState42
    act = retransmitn1n1k1v1NUM1
}

one sig PosState9 extends PosState {} {
    prevState = PosState7
    act = reshardn1n1k2v1NUM1
}

one sig PosState29 extends PosState {} {
    prevState = PosState7
    act = reshardn1n2k1v1NUM1
}

one sig PosState34 extends PosState {} {
    prevState = PosState7
    act = reshardn1n1k1v1NUM1
}

one sig PosState35 extends PosState {} {
    prevState = PosState34
    act = reshardn1n1k1v1NUM2
}

one sig PosState47 extends PosState {} {
    prevState = PosState34
    act = reshardn2n2k1v1NUM1
}

one sig PosState41 extends PosState {} {
    prevState = PosState7
    act = reshardn2n2k2v1NUM1
}

one sig PosState32 extends PosState {} {
    prevState = PosState7
    act = reshardn1n1k1v2NUM1
}

one sig PosState33 extends PosState {} {
    prevState = PosState32
    act = reshardn2n2k1v2NUM1
}

one sig PosState8 extends PosState {} {
    prevState = PosState7
    act = reshardn2n2k1v1NUM1
}

one sig PosState30 extends PosState {} {
    prevState = PosState2
    act = reshardn1n1k1v2NUM1
}

one sig PosState37 extends PosState {} {
    prevState = PosState30
    act = retransmitn1n1k1v1NUM1
}

one sig PosState15 extends PosState {} {
    prevState = PosState2
    act = reshardn2n2k1v1NUM1
}

one sig PosState16 extends PosState {} {
    prevState = PosState15
    act = retransmitn1n1k1v1NUM1
}

one sig PosState10 extends PosState {} {
    prevState = PosState1
    act = reshardn1n1k1v1NUM2
}

one sig PosState21 extends PosState {} {
    prevState = PosState10
    act = reshardn2n1k1v1NUM2
}

one sig PosState26 extends PosState {} {
    prevState = PosState10
    act = reshardn1n2k1v1NUM1
}

one sig PosState27 extends PosState {} {
    prevState = PosState26
    act = retransmitn1n2k1v1NUM1
}

one sig PosState11 extends PosState {} {
    prevState = PosState10
    act = reshardn1n1k1v1NUM1
}

one sig PosState12 extends PosState {} {
    prevState = PosState11
    act = reshardn1n1k1v1NUM1
}

one sig PosState13 extends PosState {} {
    prevState = PosState12
    act = retransmitn1n1k1v1NUM1
}

one sig PosState17 extends PosState {} {
    prevState = PosState11
    act = retransmitn1n1k1v1NUM1
}

one sig PosState14 extends PosState {} {
    prevState = PosState11
    act = retransmitn1n1k1v1NUM2
}

one sig PosState39 extends PosState {} {
    prevState = PosState10
    act = reshardn1n1k1v1NUM2
}

one sig PosState40 extends PosState {} {
    prevState = PosState39
    act = retransmitn1n1k1v1NUM2
}

one sig PosState31 extends PosState {} {
    prevState = PosState10
    act = retransmitn1n1k1v1NUM2
}


