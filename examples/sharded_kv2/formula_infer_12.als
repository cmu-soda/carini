//22
//12
open util/boolean
open util/boolean
open util/ordering[Idx] as IdxOrder
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
	children : set Target
}

sig TT, FF extends Target {} {
	no children
}

sig NotTarget extends Target {
	child : Formula
} {
	children = child
	child in TT + FF // for now
}

// a Fluent within a target formula
sig FluentTarget extends Target {
    fluent : Fluent,
    action : FlSymAction,
    wrappingAction : FlSymAction,
    flToActParamsMap : set(ParamIdx->ParamIdx)
} {
    no children
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
	all f : Target | f not in f.^children // the DAG requirement
	no FlSymAction.target.(~children) // the targets have no parents
	Target = FlSymAction.target.*children // all Targets must be part of a target formula

    // specify the action that wraps each FluentTarget
    all w : FluentTarget, s : FlSymAction | (w in s.target.*children) implies (w.wrappingAction = s)
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

abstract sig Idx {}

abstract sig Trace {
	path : Idx -> Act, // the path for the trace
	lastIdx : Idx, // the last index in the path for the trace
	initiates : Env -> Idx -> FlSymAction, // the actions that initiate fluent values
	terminates : Env -> Idx -> FlSymAction, // the actions that terminate fluent values
	satisfies : Env -> Idx -> Formula, // formulas that satisfy this trace (state-based semantics)
	targetSat : Idx -> Target
} {
    // Target formulas
	all i : Idx, f : TT | i->f in targetSat
	all i : Idx, f : FF | i->f not in targetSat
	all i : Idx, f : NotTarget | i->f in targetSat iff (i->f.child not in targetSat)
	all i : Idx, f : FluentTarget | i->f in targetSat iff
        let a = i.path |
        let flEnv = { env : Env | (~(f.fluent.vars)).(f.flToActParamsMap).(a.params) = env.maps } |
            some flEnv and flEnv->i->f.fluent in satisfies


    // fluent actions that initiate
    all e : Env, i : Idx, s : FlSymAction | e->i->s in initiates iff
        let a = i.path |
        let isInitAct = some s and concreteMatchesSymAction[e,a,s] and i->s.target in targetSat |
        let isTermAct = some s and concreteMatchesSymAction[e,a,s] and i->s.target not in targetSat |
        let sPrev = previousPriorityFlSymAction[s] |
            isInitAct
            or
            (not isTermAct and some sPrev and e->i->sPrev in initiates)

    // fluent actions that terminate
    all e : Env, i : Idx, s : FlSymAction | e->i->s in terminates iff
        let a = i.path |
        let isInitAct = some s and concreteMatchesSymAction[e,a,s] and i->s.target in targetSat |
        let isTermAct = some s and concreteMatchesSymAction[e,a,s] and i->s.target not in targetSat |
        let sPrev = previousPriorityFlSymAction[s] |
            isTermAct
            or
            (not isInitAct and some sPrev and e->i->sPrev in terminates)


	// state-based trace semantics
	// i refers to the index right before the action
	// e |- t,i |= f, where e is an environment, t is a trace, i is an index, and f is a formula
	all e : Env, i : Idx, f : Not | e->i->f in satisfies iff (e->i->f.child not in satisfies)
	all e : Env, i : Idx, f : Implies | e->i->f in satisfies iff (e->i->f.left in satisfies implies e->i->f.right in satisfies)
	all e : Env, i : Idx, f : VarEquals | e->i->f in satisfies iff (f.lhs).(e.maps) = (f.rhs).(e.maps)
	all e : Env, i : Idx, f : VarSetContains | e->i->f in satisfies iff setContains[(f.theSet).(e.maps), (f.elem).(e.maps)]
	all e : Env, i : Idx, f : VarLTE | e->i->f in satisfies iff lte[(f.lhs).(e.maps), (f.rhs).(e.maps)]

    all e : Env, i : Idx, f : Fluent | e->i->f in satisfies iff
        let a = (i.prev).path |
        let s = highestPriorityFlSymAction[f,a] |
        let isInitAct = some s and concreteMatchesSymAction[e,a,s] and some i.prev and e->i.prev->s in initiates |
        let isTermAct = some s and concreteMatchesSymAction[e,a,s] and some i.prev and e->i.prev->s in terminates |
            (no i.prev and f.initially = True) or
            (isInitAct) or
            (not isTermAct and some i.prev and e->i.prev->f in satisfies)

	all e : Env, i : Idx, f : Forall | e->i->f in satisfies iff
		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Exists | e->i->f in satisfies iff
		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Root | e->i->f in satisfies iff e->i->f.children in satisfies
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

fun indices[t : Trace] : set Idx {
	t.lastIdx.*(~IdxOrder/next)
}

fun rangeParamIdx[p : ParamIdx] : set ParamIdx {
	p.*(~ParamIdxOrder/next)
}

fun rangeFlActionIdx[s : FlActionIdx] : set FlActionIdx {
	s.*(~FlActionIdxOrder/next)
}

abstract sig PosTrace extends Trace {} {}
abstract sig NegTrace extends Trace {} {}


// 'partial fluents' are fluents that do not update every param in the fluent (and hence, in practice,
// update every sort value of the missing param).
fun partialFluents : set FlSymAction {
	 { a : FlSymAction | some f : Fluent | a in f.flActions and a.flToActParamsMap.ParamIdx != f.vars.Var }
}


/* main */
run {
	// find a formula that separates "good" traces from "bad" ones
	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies
	all nt : NegTrace | no (EmptyEnv->nt.lastIdx->Root & nt.satisfies) // target the last index

	// minimization constraints
	softno partialFluents // fewer partial fluents
	softno (FlSymAction.target - (TT + FF)) // fewer targets that aren't TRUE or FALSE
	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals
	minsome flActions // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent.vars // minimize the # of params for each fluent
}
for 8 Formula, 4 FlSymAction, 4 Target

one sig P0, P1, P2, P3 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = P0->P1 + P1->P2 + P2->P3
	all f : Fluent | (f.vars.Var = P0) or (f.vars.Var = P0+P1) or (f.vars.Var = P0+P1+P2) or (f.vars.Var = P0+P1+P2+P3)
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
	let containsRel = (none->none) |
		(lhs->rhs) in containsRel
}


one sig N1, N2, K1, K2, V1, V2 extends Atom {}

one sig Value extends Sort {} {
	atoms = V1 + V2
	numericSort = False
}
one sig Key extends Sort {} {
	atoms = K1 + K2
	numericSort = False
}
one sig Node extends Sort {} {
	atoms = N1 + N2
	numericSort = False
}

one sig RecvTransferMsg extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Node + P1->Key + P2->Value
}
one sig RecvTransferMsgN1K2V2 extends Act {} {
	params = (P0->N1 + P1->K2 + P2->V2)
}
one sig RecvTransferMsgN1K1V1 extends Act {} {
	params = (P0->N1 + P1->K1 + P2->V1)
}
one sig RecvTransferMsgN2K1V2 extends Act {} {
	params = (P0->N2 + P1->K1 + P2->V2)
}
one sig RecvTransferMsgN1K1V2 extends Act {} {
	params = (P0->N1 + P1->K1 + P2->V2)
}

one sig Reshard extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3
	paramTypes = P0->Key + P1->Value + P2->Node + P3->Node
}
one sig ReshardK1V2N1N2 extends Act {} {
	params = (P0->K1 + P1->V2 + P2->N1 + P3->N2)
}
one sig ReshardK1V1N1N1 extends Act {} {
	params = (P0->K1 + P1->V1 + P2->N1 + P3->N1)
}
one sig ReshardK2V2N2N1 extends Act {} {
	params = (P0->K2 + P1->V2 + P2->N2 + P3->N1)
}


one sig T0, T1, T2, T3, T4, T5, T6 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6
	RecvTransferMsg in FlSymAction.baseName // the final base name in the neg trace must appear in the sep formula
}


fun envVarTypes : set(Var->Sort) {
	var2->Node + var1->Key + var0->Value
}


one sig var0, var1, var2 extends Var {} {}


one sig var0toV2var2toN1var1toK1 extends Env {} {}
one sig var0toV1var2toN1var1toK2 extends Env {} {}
one sig var2toN2var0toV1var1toK1 extends Env {} {}
one sig var0toV1var2toN1var1toK1 extends Env {} {}
one sig var0toV2var2toN1var1toK2 extends Env {} {}
one sig var2toN2var0toV2var1toK1 extends Env {} {}
one sig var2toN2var0toV1var1toK2 extends Env {} {}
one sig var0toV2var1toK2 extends Env {} {}
one sig var0toV1var1toK1 extends Env {} {}
one sig var0toV1 extends Env {} {}
one sig var0toV2var1toK1 extends Env {} {}
one sig var0toV1var1toK2 extends Env {} {}
one sig var0toV2 extends Env {} {}
one sig var2toN2var0toV2var1toK2 extends Env {} {}


fact PartialInstance {
	lastIdx = (PT1->T6) + (NT1->T6)

	path = (PT1 -> (T0->ReshardK1V1N1N1 + T1->RecvTransferMsgN1K1V1 + T2->ReshardK1V2N1N2 + T3->RecvTransferMsgN2K1V2 + T4->ReshardK2V2N2N1 + T5->RecvTransferMsgN1K2V2)) +
		(NT1 -> (T0->ReshardK1V1N1N1 + T1->RecvTransferMsgN1K1V1 + T2->ReshardK1V2N1N2 + T3->RecvTransferMsgN2K1V2 + T4->ReshardK2V2N2N1 + T5->RecvTransferMsgN1K1V2))

	maps = var0toV2var2toN1var1toK1->(var0->V2 + var2->N1 + var1->K1) +
		var0toV1var2toN1var1toK2->(var0->V1 + var2->N1 + var1->K2) +
		var2toN2var0toV1var1toK1->(var2->N2 + var0->V1 + var1->K1) +
		var0toV1var2toN1var1toK1->(var0->V1 + var2->N1 + var1->K1) +
		var0toV2var2toN1var1toK2->(var0->V2 + var2->N1 + var1->K2) +
		var2toN2var0toV2var1toK1->(var2->N2 + var0->V2 + var1->K1) +
		var2toN2var0toV1var1toK2->(var2->N2 + var0->V1 + var1->K2) +
		var0toV2var1toK2->(var0->V2 + var1->K2) +
		var0toV1var1toK1->(var0->V1 + var1->K1) +
		var0toV1->(var0->V1) +
		var0toV2var1toK1->(var0->V2 + var1->K1) +
		var0toV1var1toK2->(var0->V1 + var1->K2) +
		var0toV2->(var0->V2) +
		var2toN2var0toV2var1toK2->(var2->N2 + var0->V2 + var1->K2)

	baseName = ReshardK1V2N1N2->Reshard +
		RecvTransferMsgN1K1V1->RecvTransferMsg +
		RecvTransferMsgN1K1V2->RecvTransferMsg +
		ReshardK2V2N2N1->Reshard +
		RecvTransferMsgN1K2V2->RecvTransferMsg +
		ReshardK1V1N1N1->Reshard +
		RecvTransferMsgN2K1V2->RecvTransferMsg
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT1 extends PosTrace {} {}
