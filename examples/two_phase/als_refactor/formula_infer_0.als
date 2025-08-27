//15
//0
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


/* Formula signatures (represented by a DAG) */
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

    // cumulative map, including lower priorities
    prioritizedFlToActParamsMap : set(ParamIdx->ParamIdx),

    value : Bool, // init v. term

    // the 'priority' of the action, which matters when there's multiple FlSymActions
    // with the same base action.
    flActIdx : FlActionIdx
} {
    // domain(flToActParamsMap) must be a sequence of P0, P1, ... (i.e. no gaps between param numbers)
    (no flToActParamsMap) or (P0 in flToActParamsMap.ParamIdx)
    (flToActParamsMap.ParamIdx).*(~ParamIdxOrder/next) = flToActParamsMap.ParamIdx

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

    // each param to the fluent must be used by some fl action
    (flActions.flToActParamsMap).ParamIdx = vars.Var

    // vars is a function
    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)

    // each action must input the same param-types to the fluent
    let flParamTypes = vars.envVarTypes |
        all a : flActions |
            // for each param in the action, its type must match the fluent
            all actIdx : ParamIdx.(a.flToActParamsMap) |
                let flIdx = (a.flToActParamsMap).actIdx |
                    flIdx.flParamTypes = actIdx.(a.baseName.paramTypes)

    // For each 'category' of FlSymAction's (the FlSymAction's that share the same base name), they must:
    // 1. have different orderings (priorities) and
    // 2. their orderings must form a sequence from 0 up to the max idx
    all actName : BaseName |
        let flActCategory = { a : flActions | a.baseName = actName } |
        let maxIdx = FlActionIdxOrder/max[flActCategory.flActIdx] |
            (all a1,a2 : flActCategory | (a1.flActIdx = a2.flActIdx implies a1=a2)) and
            (flActCategory.flActIdx = rangeFlActionIdx[maxIdx])
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

fact {
	// the following two facts make sure that the formulas create a tree (i.e. DAG w/o 'diamond' structures)
	no Root.(~children) // the root has no parents
	all f : (Formula - Root) | one f.(~children) // all non-root formulas have exactly one parent
	all f : Formula | f in Root.*children // all Formulas must be part of the overall formula
	Fluent.flActions = FlSymAction // all FlSymActions must be in fluents
	all f1,f2 : Fluent, a : FlSymAction | (a in f1.flActions and a in f2.flActions) implies f1 = f2 // no sharing FlSymActions

	// no free vars, all vars must be used in the matrix
	let varsInMatrix = ParamIdx.(Fluent.vars) + VarEquals.(lhs+rhs) + VarSetContains.(elem+theSet) + VarLTE.(lhs+rhs) |
		varsInMatrix = (Forall.var + Exists.var)

	// do not quantify over a variable that's already in scope
	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)

	// require lhs to not have have an Implies node
	// this is an overconstraint for improving speed
	all f : Implies | no (f.left.*children) & Implies

	(Forall+Exists).^(~children) in (Root+Forall+Exists) // prenex normal form
	some Implies // non-degenerate formulas
	FlSymAction.flActIdx = S0 + S1
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
	satisfies : Env -> Idx -> Formula // formulas that satisfy this trace
} {
	// trace semantics, i.e. e |- t,i |= f, where e is an environment, t is a trace, i is an index, and f is a formula
	all e : Env, i : Idx, f : Not | e->i->f in satisfies iff (e->i->f.child not in satisfies)
	all e : Env, i : Idx, f : Implies | e->i->f in satisfies iff (e->i->f.left in satisfies implies e->i->f.right in satisfies)
	all e : Env, i : Idx, f : VarEquals | e->i->f in satisfies iff (f.lhs).(e.maps) = (f.rhs).(e.maps)
	all e : Env, i : Idx, f : VarSetContains | e->i->f in satisfies iff setContains[(f.theSet).(e.maps), (f.elem).(e.maps)]
	all e : Env, i : Idx, f : VarLTE | e->i->f in satisfies iff lte[(f.lhs).(e.maps), (f.rhs).(e.maps)]

	// e |- t,i |= f (where f is a fluent) iff any (the disjunction) of the following three hold:
	// 1. t[i] \in f.initFl
	// 2. t[i] \notin f.termFl and i = 0 and f.initally = True
	// 3. t[i] \notin f.termFl and (e |- t,i-1 |= f)
	all e : Env, i : Idx, f : Fluent | e->i->f in satisfies iff
        // a is the action at the current index i in the trace (i.e. a = t[i])
        let a = i.path |
            (isInitAct[a,e,f]) or
            (not isTermAct[a,e,f] and no i.prev and f.initially = True) or
            (not isTermAct[a,e,f] and some i.prev and e->(i.prev)->f in satisfies)

	all e : Env, i : Idx, f : Forall | e->i->f in satisfies iff
		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Exists | e->i->f in satisfies iff
		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Root | e->i->f in satisfies iff e->i->f.children in satisfies
}

fact {
	all s : FlSymAction |
	let sPrev = {s' : FlSymAction | s'.flActIdx.next = s.flActIdx} |
	    s.prioritizedFlToActParamsMap = sPrev.prioritizedFlToActParamsMap ++ s.flToActParamsMap
}

fun highestPriorityFlAct[cat : set FlSymAction] : FlSymAction {
    { s : cat | all s' : cat | FlActionIdxOrder/gte[s.flActIdx, s'.flActIdx] }
}

// does this action initiate the fluent?
pred isInitAct[a : Act, e : Env, f : Fluent] {
    let flActCategory = { s : f.flActions | s.baseName = a.baseName } |
    let s = highestPriorityFlAct[flActCategory] |
        (s.value = True and (~(f.vars)).(s.prioritizedFlToActParamsMap).(a.params) in e.maps)
}

// does this action terminate the fluent?
pred isTermAct[a : Act, e : Env, f : Fluent] {
    let flActCategory = { s : f.flActions | s.baseName = a.baseName } |
    let s = highestPriorityFlAct[flActCategory] |
        (s.value = False and (~(f.vars)).(s.prioritizedFlToActParamsMap).(a.params) in e.maps)
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
one sig EmptyTrace extends Trace {} {
	 no path
}


	// 'partial fluents' are fluents that do not update every param in the fluent (and hence, in practice,
	// update every sort value of the missing param).
fun partialFluents : set FlSymAction {
	 { a : FlSymAction | some f : Fluent | a in f.flActions and a.flToActParamsMap.ParamIdx != f.vars.Var }
}


/* main */
run {
	// find a formula that separates "good" traces from "bad" ones
	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies
	all nt : NegTrace | no (EmptyEnv->nt.lastIdx->Root & nt.satisfies)
	EmptyEnv->T0->Root in EmptyTrace.satisfies // the formula must satisfy the empty trace

	// minimization constraints
	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals
	minsome flActions // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent.vars // minimize the # of params for each fluent
}
for 8 Formula, 4 FlSymAction

one sig P0 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = none->none
	all f : Fluent | (f.vars.Var = P0)
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


one sig r2, r3, r1 extends Atom {}

one sig RMs extends Sort {} {
	atoms = r2 + r3 + r1
	numericSort = False
}

one sig SndPrepare extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig SndPreparer3 extends Act {} {
	params = (P0->r3)
}
one sig SndPreparer1 extends Act {} {
	params = (P0->r1)
}
one sig SndPreparer2 extends Act {} {
	params = (P0->r2)
}

one sig RcvAbort extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}


one sig RcvCommit extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig RcvCommitr1 extends Act {} {
	params = (P0->r1)
}


one sig T0, T1, T2, T3 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3
	RcvCommit in FlSymAction.baseName // the final base name in the neg trace must appear in the sep formula
}


fun envVarTypes : set(Var->Sort) {
	var2->RMs + var1->RMs + var0->RMs
}


one sig var2, var1, var0 extends Var {} {}


one sig var0tor3 extends Env {} {}
one sig var0tor3var1tor3 extends Env {} {}
one sig var0tor3var1tor3var2tor3 extends Env {} {}
one sig var0tor3var1tor3var2tor2 extends Env {} {}
one sig var0tor3var1tor2var2tor3 extends Env {} {}
one sig var1tor3var0tor2var2tor3 extends Env {} {}
one sig var0tor3var1tor2 extends Env {} {}
one sig var1tor3var0tor2 extends Env {} {}
one sig var0tor2 extends Env {} {}
one sig var0tor1 extends Env {} {}
one sig var1tor2var0tor2 extends Env {} {}
one sig var1tor3var0tor1 extends Env {} {}
one sig var0tor3var1tor1 extends Env {} {}
one sig var0tor3var1tor2var2tor2 extends Env {} {}
one sig var1tor3var2tor2var0tor2 extends Env {} {}
one sig var1tor2var0tor2var2tor3 extends Env {} {}
one sig var1tor3var0tor1var2tor3 extends Env {} {}
one sig var0tor3var1tor1var2tor3 extends Env {} {}
one sig var0tor3var1tor3var2tor1 extends Env {} {}
one sig var1tor2var0tor1 extends Env {} {}
one sig var0tor2var1tor1 extends Env {} {}
one sig var0tor1var1tor1 extends Env {} {}
one sig var2tor1var0tor1var1tor1 extends Env {} {}
one sig var1tor2var2tor2var0tor2 extends Env {} {}
one sig var1tor3var2tor2var0tor1 extends Env {} {}
one sig var0tor3var2tor2var1tor1 extends Env {} {}
one sig var1tor2var0tor1var2tor3 extends Env {} {}
one sig var0tor2var1tor1var2tor3 extends Env {} {}
one sig var0tor3var1tor2var2tor1 extends Env {} {}
one sig var1tor3var0tor2var2tor1 extends Env {} {}
one sig var1tor2var2tor2var0tor1 extends Env {} {}
one sig var2tor2var0tor2var1tor1 extends Env {} {}
one sig var0tor1var1tor1var2tor3 extends Env {} {}
one sig var1tor2var0tor2var2tor1 extends Env {} {}
one sig var1tor3var2tor1var0tor1 extends Env {} {}
one sig var0tor3var2tor1var1tor1 extends Env {} {}
one sig var2tor2var0tor1var1tor1 extends Env {} {}
one sig var1tor2var2tor1var0tor1 extends Env {} {}
one sig var0tor2var2tor1var1tor1 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT2->T3) + (PT1->T1) + (NT1->T1)

	path = (PT2 -> (T0->SndPreparer1 + T1->SndPreparer2 + T2->SndPreparer3 + T3->RcvCommitr1)) +
		(PT1 -> (T0->SndPreparer1 + T1->SndPreparer1)) +
		(NT1 -> (T0->SndPreparer1 + T1->RcvCommitr1))

	maps = var0tor3->(var0->r3) +
		var0tor3var1tor3->(var0->r3 + var1->r3) +
		var0tor3var1tor3var2tor3->(var0->r3 + var1->r3 + var2->r3) +
		var0tor3var1tor3var2tor2->(var0->r3 + var1->r3 + var2->r2) +
		var0tor3var1tor2var2tor3->(var0->r3 + var1->r2 + var2->r3) +
		var1tor3var0tor2var2tor3->(var1->r3 + var0->r2 + var2->r3) +
		var0tor3var1tor2->(var0->r3 + var1->r2) +
		var1tor3var0tor2->(var1->r3 + var0->r2) +
		var0tor2->(var0->r2) +
		var0tor1->(var0->r1) +
		var1tor2var0tor2->(var1->r2 + var0->r2) +
		var1tor3var0tor1->(var1->r3 + var0->r1) +
		var0tor3var1tor1->(var0->r3 + var1->r1) +
		var0tor3var1tor2var2tor2->(var0->r3 + var1->r2 + var2->r2) +
		var1tor3var2tor2var0tor2->(var1->r3 + var2->r2 + var0->r2) +
		var1tor2var0tor2var2tor3->(var1->r2 + var0->r2 + var2->r3) +
		var1tor3var0tor1var2tor3->(var1->r3 + var0->r1 + var2->r3) +
		var0tor3var1tor1var2tor3->(var0->r3 + var1->r1 + var2->r3) +
		var0tor3var1tor3var2tor1->(var0->r3 + var1->r3 + var2->r1) +
		var1tor2var0tor1->(var1->r2 + var0->r1) +
		var0tor2var1tor1->(var0->r2 + var1->r1) +
		var0tor1var1tor1->(var0->r1 + var1->r1) +
		var2tor1var0tor1var1tor1->(var2->r1 + var0->r1 + var1->r1) +
		var1tor2var2tor2var0tor2->(var1->r2 + var2->r2 + var0->r2) +
		var1tor3var2tor2var0tor1->(var1->r3 + var2->r2 + var0->r1) +
		var0tor3var2tor2var1tor1->(var0->r3 + var2->r2 + var1->r1) +
		var1tor2var0tor1var2tor3->(var1->r2 + var0->r1 + var2->r3) +
		var0tor2var1tor1var2tor3->(var0->r2 + var1->r1 + var2->r3) +
		var0tor3var1tor2var2tor1->(var0->r3 + var1->r2 + var2->r1) +
		var1tor3var0tor2var2tor1->(var1->r3 + var0->r2 + var2->r1) +
		var1tor2var2tor2var0tor1->(var1->r2 + var2->r2 + var0->r1) +
		var2tor2var0tor2var1tor1->(var2->r2 + var0->r2 + var1->r1) +
		var0tor1var1tor1var2tor3->(var0->r1 + var1->r1 + var2->r3) +
		var1tor2var0tor2var2tor1->(var1->r2 + var0->r2 + var2->r1) +
		var1tor3var2tor1var0tor1->(var1->r3 + var2->r1 + var0->r1) +
		var0tor3var2tor1var1tor1->(var0->r3 + var2->r1 + var1->r1) +
		var2tor2var0tor1var1tor1->(var2->r2 + var0->r1 + var1->r1) +
		var1tor2var2tor1var0tor1->(var1->r2 + var2->r1 + var0->r1) +
		var0tor2var2tor1var1tor1->(var0->r2 + var2->r1 + var1->r1)

	baseName = SndPreparer2->SndPrepare +
		SndPreparer3->SndPrepare +
		SndPreparer1->SndPrepare +
		RcvCommitr1->RcvCommit
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT2 extends PosTrace {} {}
one sig PT1 extends PosTrace {} {}
