//22
//19
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
	params : ParamIdx->Atom,
	initiates : Env->Fluent->FlActionIdx,
	terminates : Env->Fluent->FlActionIdx
}

fact {
    // initiation for a concrete action (Act)
    all e : Env, a : Act, f : Fluent, si : FlActionIdx | e->f->si in a.initiates iff
        (initiation[e,a,f,si]
        or
        (not termination[e,a,f,si] and some si.prev and e->f->(si.prev) in a.initiates))

    // termination for a concrete action (Act)
    all e : Env, a : Act, f : Fluent, si : FlActionIdx | e->f->si in a.terminates iff
        (termination[e,a,f,si]
        or
        (not initiation[e,a,f,si] and some si.prev and e->f->(si.prev) in a.terminates))
}

pred initiation[e : Env, a : Act, f : Fluent, si : FlActionIdx] {
    let s = { s : f.flActions | s.baseName = a.baseName and s.flActIdx = si } |
        initiation[e,a,f,s]
}

pred initiation[e : Env, a : Act, f : Fluent, s : FlSymAction] {
    s.value = True and (~(f.vars)).(s.flToActParamsMap).(a.params) in e.maps
}

pred termination[e : Env, a : Act, f : Fluent, si : FlActionIdx] {
    let s = { s : f.flActions | s.baseName = a.baseName and s.flActIdx = si } |
        termination[e,a,f,s]
}

pred termination[e : Env, a : Act, f : Fluent, s : FlSymAction] {
    s.value = False and (~(f.vars)).(s.flToActParamsMap).(a.params) in e.maps
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

	// no free vars, all vars must be used in the matrix
	let varsInMatrix = ParamIdx.(Fluent.vars) + VarEquals.(lhs+rhs) + VarSetContains.(elem+theSet) + VarLTE.(lhs+rhs) |
		varsInMatrix = (Forall.var + Exists.var)

	// do not quantify over a variable that's already in scope
	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)

	(Forall+Exists).^(~children) in (Root+Forall+Exists) // prenex normal form
	some Implies // avoid degenerate formulas
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

fun highestPriority[cat : set FlSymAction] : FlActionIdx {
    { s : cat | all s' : cat | FlActionIdxOrder/gte[s.flActIdx, s'.flActIdx] }.flActIdx
}

// does this action initiate the fluent?
pred isInitAct[a : Act, e : Env, f : Fluent] {
    let flActCategory = { s : f.flActions | s.baseName = a.baseName } |
    let si = highestPriority[flActCategory] |
        some si and e->f->si in a.initiates
}

// does this action terminate the fluent?
pred isTermAct[a : Act, e : Env, f : Fluent] {
    let flActCategory = { s : f.flActions | s.baseName = a.baseName } |
    let si = highestPriority[flActCategory] |
        some si and e->f->si in a.terminates
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

// calculates the indices that are larger than the minimum violating index for the negative trace.
// this function assumes there's exactly 1 negative trace in this Alloy spec.
fun violatingIdxsInNegTrace : set Idx {
	 let violatingIdxs = univ.(EmptyEnv->indices[NegTrace]->Root - NegTrace.satisfies).univ |
	  violatingIdxs + IdxOrder/nexts[violatingIdxs]
}


/* main */
run {
	// find a formula that separates "good" traces from "bad" ones
	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies
	all nt : NegTrace | EmptyEnv->indices[nt]->Root not in nt.satisfies
	EmptyEnv->T0->Root in EmptyTrace.satisfies // the formula must satisfy the empty trace

	// minimization constraints
	softno partialFluents // fewer partial fluents
	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals
	minsome flActions // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent.vars // minimize the # of params for each fluent
	maxsome violatingIdxsInNegTrace // minimize the index in the neg trace that we block (maxsome is CORRECT)
}
for 8 Formula, 5 FlSymAction

one sig P0, P1, P2 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = P0->P1 + P1->P2
	all f : Fluent | (f.vars.Var = P0) or (f.vars.Var = P0+P1) or (f.vars.Var = P0+P1+P2)
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
	let containsRel = (NUM0->NUM0 + NUM0->NUM1 + NUM0->NUM2 + NUM1->NUM1 + NUM1->NUM2 + NUM2->NUM2) |
		(lhs->rhs) in containsRel
}


one sig a1, a2, a3, NUM2, v1, v2, NUM0, NUM1 extends Atom {}

one sig Value extends Sort {} {
	atoms = v1 + v2
	numericSort = False
}
one sig Acceptor extends Sort {} {
	atoms = a1 + a2 + a3
	numericSort = False
}
one sig Ballot extends Sort {} {
	atoms = NUM2 + NUM0 + NUM1
	numericSort = True
}

one sig Phase1b extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Acceptor + P1->Ballot
}
one sig Phase1ba1NUM1 extends Act {} {
	params = (P0->a1 + P1->NUM1)
}
one sig Phase1ba1NUM2 extends Act {} {
	params = (P0->a1 + P1->NUM2)
}
one sig Phase1ba2NUM0 extends Act {} {
	params = (P0->a2 + P1->NUM0)
}
one sig Phase1ba2NUM1 extends Act {} {
	params = (P0->a2 + P1->NUM1)
}
one sig Phase1ba1NUM0 extends Act {} {
	params = (P0->a1 + P1->NUM0)
}

one sig Phase2b extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Acceptor + P1->Ballot + P2->Value
}
one sig Phase2ba1NUM1v2 extends Act {} {
	params = (P0->a1 + P1->NUM1 + P2->v2)
}
one sig Phase2ba2NUM1v1 extends Act {} {
	params = (P0->a2 + P1->NUM1 + P2->v1)
}
one sig Phase2ba1NUM0v1 extends Act {} {
	params = (P0->a1 + P1->NUM0 + P2->v1)
}
one sig Phase2ba2NUM0v1 extends Act {} {
	params = (P0->a2 + P1->NUM0 + P2->v1)
}
one sig Phase2ba2NUM1v2 extends Act {} {
	params = (P0->a2 + P1->NUM1 + P2->v2)
}
one sig Phase2ba1NUM0v2 extends Act {} {
	params = (P0->a1 + P1->NUM0 + P2->v2)
}
one sig Phase2ba2NUM0v2 extends Act {} {
	params = (P0->a2 + P1->NUM0 + P2->v2)
}
one sig Phase2ba3NUM1v2 extends Act {} {
	params = (P0->a3 + P1->NUM1 + P2->v2)
}
one sig Phase2ba3NUM0v1 extends Act {} {
	params = (P0->a3 + P1->NUM0 + P2->v1)
}
one sig Phase2ba3NUM0v2 extends Act {} {
	params = (P0->a3 + P1->NUM0 + P2->v2)
}
one sig Phase2ba1NUM2v1 extends Act {} {
	params = (P0->a1 + P1->NUM2 + P2->v1)
}
one sig Phase2ba1NUM1v1 extends Act {} {
	params = (P0->a1 + P1->NUM1 + P2->v1)
}
one sig Phase2ba1NUM2v2 extends Act {} {
	params = (P0->a1 + P1->NUM2 + P2->v2)
}

one sig Phase2a extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Ballot + P1->Value + P2->Acceptor
}
one sig Phase2aNUM1v2a3 extends Act {} {
	params = (P0->NUM1 + P1->v2 + P2->a3)
}
one sig Phase2aNUM1v1a2 extends Act {} {
	params = (P0->NUM1 + P1->v1 + P2->a2)
}
one sig Phase2aNUM2v2a2 extends Act {} {
	params = (P0->NUM2 + P1->v2 + P2->a2)
}
one sig Phase2aNUM2v1a1 extends Act {} {
	params = (P0->NUM2 + P1->v1 + P2->a1)
}
one sig Phase2aNUM0v2a1 extends Act {} {
	params = (P0->NUM0 + P1->v2 + P2->a1)
}
one sig Phase2aNUM0v1a2 extends Act {} {
	params = (P0->NUM0 + P1->v1 + P2->a2)
}
one sig Phase2aNUM1v2a2 extends Act {} {
	params = (P0->NUM1 + P1->v2 + P2->a2)
}
one sig Phase2aNUM1v1a1 extends Act {} {
	params = (P0->NUM1 + P1->v1 + P2->a1)
}
one sig Phase2aNUM0v1a1 extends Act {} {
	params = (P0->NUM0 + P1->v1 + P2->a1)
}
one sig Phase2aNUM1v2a1 extends Act {} {
	params = (P0->NUM1 + P1->v2 + P2->a1)
}


one sig T0, T1, T2, T3, T4, T5, T6, T7, T8, T9 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6 + T6->T7 + T7->T8 + T8->T9
}


fun envVarTypes : set(Var->Sort) {
	var2->Ballot + var1->Acceptor + var0->Acceptor
}


one sig var0, var1, var2 extends Var {} {}


one sig var0toa3var1toa2 extends Env {} {}
one sig var1toa3var0toa2 extends Env {} {}
one sig var0toa3var1toa2var2toNUM2 extends Env {} {}
one sig var1toa3var2toNUM2var0toa2 extends Env {} {}
one sig var0toa3var1toa3var2toNUM1 extends Env {} {}
one sig var0toa3var1toa3var2toNUM2 extends Env {} {}
one sig var0toa3var1toa3 extends Env {} {}
one sig var0toa3var1toa1var2toNUM2 extends Env {} {}
one sig var1toa2var2toNUM2var0toa2 extends Env {} {}
one sig var1toa3var0toa1var2toNUM2 extends Env {} {}
one sig var0toa3var2toNUM0var1toa3 extends Env {} {}
one sig var0toa3var2toNUM1var1toa2 extends Env {} {}
one sig var1toa3var2toNUM1var0toa2 extends Env {} {}
one sig var0toa1 extends Env {} {}
one sig var0toa2 extends Env {} {}
one sig var0toa3 extends Env {} {}
one sig var0toa1var1toa1var2toNUM2 extends Env {} {}
one sig var0toa3var2toNUM0var1toa1 extends Env {} {}
one sig var2toNUM0var1toa2var0toa2 extends Env {} {}
one sig var2toNUM0var1toa3var0toa1 extends Env {} {}
one sig var2toNUM1var1toa1var0toa2 extends Env {} {}
one sig var0toa1var2toNUM1var1toa2 extends Env {} {}
one sig var0toa1var1toa1 extends Env {} {}
one sig var1toa1var2toNUM2var0toa2 extends Env {} {}
one sig var0toa1var1toa2var2toNUM2 extends Env {} {}
one sig var0toa3var2toNUM0var1toa2 extends Env {} {}
one sig var2toNUM0var1toa3var0toa2 extends Env {} {}
one sig var0toa3var2toNUM1var1toa1 extends Env {} {}
one sig var2toNUM1var1toa2var0toa2 extends Env {} {}
one sig var1toa3var0toa1var2toNUM1 extends Env {} {}
one sig var2toNUM0var0toa1var1toa1 extends Env {} {}
one sig var1toa1var0toa2 extends Env {} {}
one sig var0toa1var1toa2 extends Env {} {}
one sig var0toa3var1toa1 extends Env {} {}
one sig var1toa2var0toa2 extends Env {} {}
one sig var1toa3var0toa1 extends Env {} {}
one sig var2toNUM0var1toa1var0toa2 extends Env {} {}
one sig var2toNUM0var0toa1var1toa2 extends Env {} {}
one sig var0toa1var2toNUM1var1toa1 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT13->T4) + (PT15->T4) + (PT22->T5) + (PT16->T3) + (PT23->T4) + (PT3->T2) + (PT24->T4) + (PT20->T4) + (PT11->T4) + (PT1->T7) + (PT9->T3) + (PT6->T1) + (PT21->T4) + (PT8->T4) + (PT25->T4) + (PT19->T5) + (PT17->T3) + (PT14->T2) + (PT7->T4) + (PT12->T3) + (PT26->T2) + (PT4->T2) + (NT1->T9)

	path = (PT13 -> (T0->Phase2aNUM0v1a1 + T1->Phase1ba1NUM0 + T2->Phase2aNUM1v2a3 + T3->Phase2ba2NUM0v1 + T4->Phase2ba2NUM1v2)) +
		(PT15 -> (T0->Phase1ba1NUM2 + T1->Phase2aNUM0v1a1 + T2->Phase2aNUM1v2a3 + T3->Phase2ba2NUM0v1 + T4->Phase2ba2NUM1v2)) +
		(PT22 -> (T0->Phase2aNUM0v1a1 + T1->Phase2aNUM1v2a3 + T2->Phase2ba1NUM0v1 + T3->Phase2ba1NUM1v2 + T4->Phase2ba3NUM0v1 + T5->Phase2ba3NUM1v2)) +
		(PT16 -> (T0->Phase2aNUM0v1a1 + T1->Phase2aNUM1v2a1 + T2->Phase2ba2NUM0v1 + T3->Phase2ba2NUM1v2)) +
		(PT23 -> (T0->Phase2aNUM0v1a1 + T1->Phase1ba1NUM0 + T2->Phase2aNUM1v2a3 + T3->Phase2ba1NUM1v2 + T4->Phase2ba2NUM0v1)) +
		(PT3 -> (T0->Phase1ba1NUM0 + T1->Phase2aNUM0v1a2 + T2->Phase2ba1NUM0v1)) +
		(PT24 -> (T0->Phase1ba1NUM1 + T1->Phase2aNUM0v1a2 + T2->Phase2aNUM1v2a1 + T3->Phase2ba1NUM1v2 + T4->Phase2ba2NUM0v1)) +
		(PT20 -> (T0->Phase2aNUM0v1a1 + T1->Phase2aNUM1v2a3 + T2->Phase2ba1NUM0v1 + T3->Phase2ba1NUM1v2 + T4->Phase2ba2NUM0v1)) +
		(PT11 -> (T0->Phase1ba1NUM0 + T1->Phase1ba2NUM0 + T2->Phase2aNUM0v1a1 + T3->Phase2ba2NUM0v1 + T4->Phase2ba1NUM0v1)) +
		(PT1 -> (T0->Phase1ba1NUM0 + T1->Phase1ba1NUM1 + T2->Phase1ba2NUM0 + T3->Phase1ba2NUM1 + T4->Phase2aNUM0v2a1 + T5->Phase2aNUM1v1a1 + T6->Phase2ba1NUM1v1 + T7->Phase2ba3NUM0v2)) +
		(PT9 -> (T0->Phase2aNUM0v1a1 + T1->Phase2aNUM1v2a1 + T2->Phase2ba1NUM0v1 + T3->Phase2ba1NUM1v2)) +
		(PT6 -> (T0->Phase2aNUM0v1a1 + T1->Phase2aNUM1v1a2)) +
		(PT21 -> (T0->Phase1ba1NUM2 + T1->Phase2aNUM0v1a1 + T2->Phase2aNUM2v2a2 + T3->Phase2ba3NUM0v1 + T4->Phase2ba1NUM2v2)) +
		(PT8 -> (T0->Phase1ba1NUM1 + T1->Phase2aNUM1v1a1 + T2->Phase2ba1NUM1v1 + T3->Phase2aNUM2v2a2 + T4->Phase2ba1NUM2v2)) +
		(PT25 -> (T0->Phase1ba1NUM2 + T1->Phase2aNUM0v1a2 + T2->Phase2aNUM1v2a2 + T3->Phase2ba2NUM0v1 + T4->Phase2ba2NUM1v2)) +
		(PT19 -> (T0->Phase1ba1NUM0 + T1->Phase1ba2NUM1 + T2->Phase2aNUM0v1a1 + T3->Phase2aNUM1v2a3 + T4->Phase2ba2NUM1v2 + T5->Phase2ba1NUM0v1)) +
		(PT17 -> (T0->Phase2aNUM0v1a1 + T1->Phase2aNUM1v1a1 + T2->Phase2ba1NUM0v1 + T3->Phase2ba1NUM1v1)) +
		(PT14 -> (T0->Phase1ba1NUM1 + T1->Phase2aNUM2v1a1 + T2->Phase2ba1NUM2v1)) +
		(PT7 -> (T0->Phase2aNUM0v1a1 + T1->Phase1ba1NUM0 + T2->Phase2aNUM1v2a3 + T3->Phase2ba1NUM0v1 + T4->Phase2ba1NUM1v2)) +
		(PT12 -> (T0->Phase2aNUM0v1a1 + T1->Phase2aNUM1v2a1 + T2->Phase2ba1NUM0v1 + T3->Phase2ba1NUM1v2)) +
		(PT26 -> (T0->Phase1ba1NUM0 + T1->Phase2aNUM1v1a2 + T2->Phase2ba1NUM1v1)) +
		(PT4 -> (T0->Phase1ba1NUM0 + T1->Phase2aNUM0v1a2 + T2->Phase2ba1NUM0v1)) +
		(NT1 -> (T0->Phase1ba1NUM0 + T1->Phase1ba1NUM1 + T2->Phase1ba2NUM0 + T3->Phase1ba2NUM1 + T4->Phase2aNUM0v2a1 + T5->Phase2aNUM1v1a1 + T6->Phase2ba1NUM1v1 + T7->Phase2ba1NUM0v2 + T8->Phase2ba2NUM0v2 + T9->Phase2ba2NUM1v1))

	maps = var0toa3var1toa2->(var0->a3 + var1->a2) +
		var1toa3var0toa2->(var1->a3 + var0->a2) +
		var0toa3var1toa2var2toNUM2->(var0->a3 + var1->a2 + var2->NUM2) +
		var1toa3var2toNUM2var0toa2->(var1->a3 + var2->NUM2 + var0->a2) +
		var0toa3var1toa3var2toNUM1->(var0->a3 + var1->a3 + var2->NUM1) +
		var0toa3var1toa3var2toNUM2->(var0->a3 + var1->a3 + var2->NUM2) +
		var0toa3var1toa3->(var0->a3 + var1->a3) +
		var0toa3var1toa1var2toNUM2->(var0->a3 + var1->a1 + var2->NUM2) +
		var1toa2var2toNUM2var0toa2->(var1->a2 + var2->NUM2 + var0->a2) +
		var1toa3var0toa1var2toNUM2->(var1->a3 + var0->a1 + var2->NUM2) +
		var0toa3var2toNUM0var1toa3->(var0->a3 + var2->NUM0 + var1->a3) +
		var0toa3var2toNUM1var1toa2->(var0->a3 + var2->NUM1 + var1->a2) +
		var1toa3var2toNUM1var0toa2->(var1->a3 + var2->NUM1 + var0->a2) +
		var0toa1->(var0->a1) +
		var0toa2->(var0->a2) +
		var0toa3->(var0->a3) +
		var0toa1var1toa1var2toNUM2->(var0->a1 + var1->a1 + var2->NUM2) +
		var0toa3var2toNUM0var1toa1->(var0->a3 + var2->NUM0 + var1->a1) +
		var2toNUM0var1toa2var0toa2->(var2->NUM0 + var1->a2 + var0->a2) +
		var2toNUM0var1toa3var0toa1->(var2->NUM0 + var1->a3 + var0->a1) +
		var2toNUM1var1toa1var0toa2->(var2->NUM1 + var1->a1 + var0->a2) +
		var0toa1var2toNUM1var1toa2->(var0->a1 + var2->NUM1 + var1->a2) +
		var0toa1var1toa1->(var0->a1 + var1->a1) +
		var1toa1var2toNUM2var0toa2->(var1->a1 + var2->NUM2 + var0->a2) +
		var0toa1var1toa2var2toNUM2->(var0->a1 + var1->a2 + var2->NUM2) +
		var0toa3var2toNUM0var1toa2->(var0->a3 + var2->NUM0 + var1->a2) +
		var2toNUM0var1toa3var0toa2->(var2->NUM0 + var1->a3 + var0->a2) +
		var0toa3var2toNUM1var1toa1->(var0->a3 + var2->NUM1 + var1->a1) +
		var2toNUM1var1toa2var0toa2->(var2->NUM1 + var1->a2 + var0->a2) +
		var1toa3var0toa1var2toNUM1->(var1->a3 + var0->a1 + var2->NUM1) +
		var2toNUM0var0toa1var1toa1->(var2->NUM0 + var0->a1 + var1->a1) +
		var1toa1var0toa2->(var1->a1 + var0->a2) +
		var0toa1var1toa2->(var0->a1 + var1->a2) +
		var0toa3var1toa1->(var0->a3 + var1->a1) +
		var1toa2var0toa2->(var1->a2 + var0->a2) +
		var1toa3var0toa1->(var1->a3 + var0->a1) +
		var2toNUM0var1toa1var0toa2->(var2->NUM0 + var1->a1 + var0->a2) +
		var2toNUM0var0toa1var1toa2->(var2->NUM0 + var0->a1 + var1->a2) +
		var0toa1var2toNUM1var1toa1->(var0->a1 + var2->NUM1 + var1->a1)

	baseName = Phase1ba2NUM1->Phase1b +
		Phase2aNUM2v1a1->Phase2a +
		Phase2aNUM2v2a2->Phase2a +
		Phase1ba2NUM0->Phase1b +
		Phase2aNUM0v1a1->Phase2a +
		Phase2ba2NUM0v1->Phase2b +
		Phase2ba2NUM1v1->Phase2b +
		Phase2ba2NUM0v2->Phase2b +
		Phase2ba2NUM1v2->Phase2b +
		Phase2aNUM0v2a1->Phase2a +
		Phase2aNUM0v1a2->Phase2a +
		Phase2ba1NUM0v2->Phase2b +
		Phase2ba1NUM1v1->Phase2b +
		Phase2ba1NUM0v1->Phase2b +
		Phase2ba1NUM2v2->Phase2b +
		Phase2ba1NUM1v2->Phase2b +
		Phase2ba1NUM2v1->Phase2b +
		Phase1ba1NUM2->Phase1b +
		Phase2aNUM1v1a2->Phase2a +
		Phase2aNUM1v2a1->Phase2a +
		Phase2aNUM1v1a1->Phase2a +
		Phase1ba1NUM0->Phase1b +
		Phase2ba3NUM1v2->Phase2b +
		Phase2aNUM1v2a3->Phase2a +
		Phase1ba1NUM1->Phase1b +
		Phase2aNUM1v2a2->Phase2a +
		Phase2ba3NUM0v1->Phase2b +
		Phase2ba3NUM0v2->Phase2b
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
}


one sig NT1 extends NegTrace {} {}

one sig PT13 extends PosTrace {} {}
one sig PT15 extends PosTrace {} {}
one sig PT22 extends PosTrace {} {}
one sig PT16 extends PosTrace {} {}
one sig PT23 extends PosTrace {} {}
one sig PT3 extends PosTrace {} {}
one sig PT24 extends PosTrace {} {}
one sig PT20 extends PosTrace {} {}
one sig PT11 extends PosTrace {} {}
one sig PT1 extends PosTrace {} {}
one sig PT9 extends PosTrace {} {}
one sig PT6 extends PosTrace {} {}
one sig PT21 extends PosTrace {} {}
one sig PT8 extends PosTrace {} {}
one sig PT25 extends PosTrace {} {}
one sig PT19 extends PosTrace {} {}
one sig PT17 extends PosTrace {} {}
one sig PT14 extends PosTrace {} {}
one sig PT7 extends PosTrace {} {}
one sig PT12 extends PosTrace {} {}
one sig PT26 extends PosTrace {} {}
one sig PT4 extends PosTrace {} {}
