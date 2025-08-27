//28
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


/* main */
run {
	// find a formula that separates "good" traces from "bad" ones
	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies
	all nt : NegTrace | no (EmptyEnv->nt.lastIdx->Root & nt.satisfies) // target the last index
	EmptyEnv->T0->Root in EmptyTrace.satisfies // the formula must satisfy the empty trace

	// minimization constraints
	softno partialFluents // fewer partial fluents
	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals
	minsome flActions // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent.vars // minimize the # of params for each fluent
}
for 9 Formula, 5 FlSymAction

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
	let containsRel = (_n2n3_->n2 + _n2n3_->n3 + _n1n2n3_->n1 + _n1n2n3_->n2 + _n1n2n3_->n3 + _n1n3_->n1 + _n1n3_->n3 + _n1n2_->n1 + _n1n2_->n2) |
		(s->e) in containsRel
}


pred isElemOfSet[e : Sort, s : Sort] {
	let elemOfRel = (Server->Quorums) |
		(e->s) in elemOfRel
}


pred lte[lhs : Atom, rhs : Atom] {
	let containsRel = (NUM0->NUM0 + NUM0->NUM1 + NUM0->NUM2 + NUM0->NUM3 + NUM1->NUM1 + NUM1->NUM2 + NUM1->NUM3 + NUM2->NUM2 + NUM2->NUM3 + NUM3->NUM3) |
		(lhs->rhs) in containsRel
}


one sig n1, n2, n3, _n2n3_, _n1n2n3_, NUM2, NUM3, _n1n3_, _n1n2_, NUM0, NUM1 extends Atom {}

one sig FinNat extends Sort {} {
	atoms = NUM2 + NUM3 + NUM0 + NUM1
	numericSort = True
}
one sig Server extends Sort {} {
	atoms = n1 + n2 + n3
	numericSort = False
}
one sig Quorums extends Sort {} {
	atoms = _n2n3_ + _n1n2n3_ + _n1n3_ + _n1n2_
	numericSort = False
}

one sig BecomeLeader extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Server + P1->FinNat
}
one sig BecomeLeadern1_n1n2n3_NUM1 extends Act {} {
	params = (P0->n1 + P1->NUM1)
}
one sig BecomeLeadern1_n1n2n3_NUM3 extends Act {} {
	params = (P0->n1 + P1->NUM3)
}
one sig BecomeLeadern2_n2n3_NUM2 extends Act {} {
	params = (P0->n2 + P1->NUM2)
}
one sig BecomeLeadern2_n2n3_NUM1 extends Act {} {
	params = (P0->n2 + P1->NUM1)
}
one sig BecomeLeadern1_n1n3_NUM2 extends Act {} {
	params = (P0->n1 + P1->NUM2)
}
one sig BecomeLeadern1_n1n2_NUM1 extends Act {} {
	params = (P0->n1 + P1->NUM1)
}
one sig BecomeLeadern1_n1n2_NUM2 extends Act {} {
	params = (P0->n1 + P1->NUM2)
}


one sig T0, T1 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1
	//ClientRequest in FlSymAction.baseName // the final base name in the neg trace must appear in the sep formula

}


fun envVarTypes : set(Var->Sort) {
	var2->Server + var1->FinNat + var0->FinNat
}


one sig var2, var1, var0 extends Var {} {}


one sig var1toNUM0var0toNUM1var2ton1 extends Env {} {}
one sig var0toNUM0var1toNUM1var2ton1 extends Env {} {}
one sig var0toNUM3 extends Env {} {}
one sig var0toNUM0var1toNUM0var2ton2 extends Env {} {}
one sig var0toNUM3var1toNUM3 extends Env {} {}
one sig var0toNUM1 extends Env {} {}
one sig var0toNUM0var1toNUM2 extends Env {} {}
one sig var1toNUM0var0toNUM2 extends Env {} {}
one sig var0toNUM1var1toNUM1 extends Env {} {}
one sig var0toNUM2var1toNUM2 extends Env {} {}
one sig var1toNUM3var0toNUM1 extends Env {} {}
one sig var0toNUM3var1toNUM1 extends Env {} {}
one sig var1toNUM0var0toNUM1 extends Env {} {}
one sig var0toNUM0var1toNUM1 extends Env {} {}
one sig var2ton3var0toNUM3var1toNUM3 extends Env {} {}
one sig var0toNUM3var1toNUM1var2ton1 extends Env {} {}
one sig var0toNUM2var2ton1var1toNUM2 extends Env {} {}
one sig var1toNUM3var0toNUM1var2ton1 extends Env {} {}
one sig var0toNUM1var2ton2var1toNUM2 extends Env {} {}
one sig var1toNUM3var0toNUM0var2ton2 extends Env {} {}
one sig var0toNUM3var1toNUM0var2ton2 extends Env {} {}
one sig var1toNUM1var2ton2var0toNUM2 extends Env {} {}
one sig var2ton3var0toNUM0var1toNUM2 extends Env {} {}
one sig var2ton3var1toNUM0var0toNUM2 extends Env {} {}
one sig var2ton3var0toNUM1var1toNUM1 extends Env {} {}
one sig var0toNUM3var1toNUM3var2ton1 extends Env {} {}
one sig var0toNUM3var2ton2var1toNUM2 extends Env {} {}
one sig var1toNUM3var2ton2var0toNUM2 extends Env {} {}
one sig var2ton3var0toNUM2var1toNUM2 extends Env {} {}
one sig var2ton3var1toNUM3var0toNUM1 extends Env {} {}
one sig var2ton3var0toNUM3var1toNUM1 extends Env {} {}
one sig var0toNUM3var1toNUM2 extends Env {} {}
one sig var1toNUM3var0toNUM2 extends Env {} {}
one sig var0toNUM0var1toNUM0var2ton1 extends Env {} {}
one sig var0toNUM2 extends Env {} {}
one sig var0toNUM0var2ton1var1toNUM2 extends Env {} {}
one sig var1toNUM0var0toNUM2var2ton1 extends Env {} {}
one sig var0toNUM1var1toNUM1var2ton1 extends Env {} {}
one sig var1toNUM0var0toNUM1var2ton2 extends Env {} {}
one sig var0toNUM0var1toNUM1var2ton2 extends Env {} {}
one sig var2ton3var0toNUM0var1toNUM0 extends Env {} {}
one sig var0toNUM1var1toNUM2 extends Env {} {}
one sig var1toNUM3var0toNUM0 extends Env {} {}
one sig var0toNUM3var1toNUM0 extends Env {} {}
one sig var1toNUM1var0toNUM2 extends Env {} {}
one sig var0toNUM3var1toNUM3var2ton2 extends Env {} {}
one sig var2ton3var0toNUM3var1toNUM2 extends Env {} {}
one sig var2ton3var1toNUM3var0toNUM2 extends Env {} {}
one sig var0toNUM0var1toNUM0 extends Env {} {}
one sig var0toNUM0 extends Env {} {}
one sig var0toNUM3var1toNUM0var2ton1 extends Env {} {}
one sig var0toNUM1var2ton1var1toNUM2 extends Env {} {}
one sig var1toNUM3var0toNUM0var2ton1 extends Env {} {}
one sig var1toNUM1var0toNUM2var2ton1 extends Env {} {}
one sig var0toNUM0var2ton2var1toNUM2 extends Env {} {}
one sig var1toNUM0var2ton2var0toNUM2 extends Env {} {}
one sig var0toNUM1var1toNUM1var2ton2 extends Env {} {}
one sig var2ton3var1toNUM0var0toNUM1 extends Env {} {}
one sig var2ton3var0toNUM0var1toNUM1 extends Env {} {}
one sig var1toNUM3var0toNUM2var2ton1 extends Env {} {}
one sig var0toNUM3var2ton1var1toNUM2 extends Env {} {}
one sig var2ton2var0toNUM2var1toNUM2 extends Env {} {}
one sig var1toNUM3var0toNUM1var2ton2 extends Env {} {}
one sig var0toNUM3var1toNUM1var2ton2 extends Env {} {}
one sig var2ton3var0toNUM1var1toNUM2 extends Env {} {}
one sig var2ton3var1toNUM3var0toNUM0 extends Env {} {}
one sig var2ton3var0toNUM3var1toNUM0 extends Env {} {}
one sig var2ton3var1toNUM1var0toNUM2 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT1->T1) + (NT1->T1)

	path = (PT1 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->BecomeLeadern2_n2n3_NUM2)) +
		(NT1 -> (T0->BecomeLeadern1_n1n2_NUM2 + T1->BecomeLeadern2_n2n3_NUM1))

	maps = var1toNUM0var0toNUM1var2ton1->(var1->NUM0 + var0->NUM1 + var2->n1) +
		var0toNUM0var1toNUM1var2ton1->(var0->NUM0 + var1->NUM1 + var2->n1) +
		var0toNUM3->(var0->NUM3) +
		var0toNUM0var1toNUM0var2ton2->(var0->NUM0 + var1->NUM0 + var2->n2) +
		var0toNUM3var1toNUM3->(var0->NUM3 + var1->NUM3) +
		var0toNUM1->(var0->NUM1) +
		var0toNUM0var1toNUM2->(var0->NUM0 + var1->NUM2) +
		var1toNUM0var0toNUM2->(var1->NUM0 + var0->NUM2) +
		var0toNUM1var1toNUM1->(var0->NUM1 + var1->NUM1) +
		var0toNUM2var1toNUM2->(var0->NUM2 + var1->NUM2) +
		var1toNUM3var0toNUM1->(var1->NUM3 + var0->NUM1) +
		var0toNUM3var1toNUM1->(var0->NUM3 + var1->NUM1) +
		var1toNUM0var0toNUM1->(var1->NUM0 + var0->NUM1) +
		var0toNUM0var1toNUM1->(var0->NUM0 + var1->NUM1) +
		var2ton3var0toNUM3var1toNUM3->(var2->n3 + var0->NUM3 + var1->NUM3) +
		var1toNUM3var0toNUM1var2ton1->(var1->NUM3 + var0->NUM1 + var2->n1) +
		var0toNUM2var2ton1var1toNUM2->(var0->NUM2 + var2->n1 + var1->NUM2) +
		var0toNUM3var1toNUM1var2ton1->(var0->NUM3 + var1->NUM1 + var2->n1) +
		var0toNUM1var2ton2var1toNUM2->(var0->NUM1 + var2->n2 + var1->NUM2) +
		var1toNUM3var0toNUM0var2ton2->(var1->NUM3 + var0->NUM0 + var2->n2) +
		var0toNUM3var1toNUM0var2ton2->(var0->NUM3 + var1->NUM0 + var2->n2) +
		var1toNUM1var2ton2var0toNUM2->(var1->NUM1 + var2->n2 + var0->NUM2) +
		var2ton3var0toNUM1var1toNUM1->(var2->n3 + var0->NUM1 + var1->NUM1) +
		var2ton3var0toNUM0var1toNUM2->(var2->n3 + var0->NUM0 + var1->NUM2) +
		var2ton3var1toNUM0var0toNUM2->(var2->n3 + var1->NUM0 + var0->NUM2) +
		var0toNUM3var1toNUM3var2ton1->(var0->NUM3 + var1->NUM3 + var2->n1) +
		var0toNUM3var2ton2var1toNUM2->(var0->NUM3 + var2->n2 + var1->NUM2) +
		var1toNUM3var2ton2var0toNUM2->(var1->NUM3 + var2->n2 + var0->NUM2) +
		var2ton3var0toNUM2var1toNUM2->(var2->n3 + var0->NUM2 + var1->NUM2) +
		var2ton3var1toNUM3var0toNUM1->(var2->n3 + var1->NUM3 + var0->NUM1) +
		var2ton3var0toNUM3var1toNUM1->(var2->n3 + var0->NUM3 + var1->NUM1) +
		var0toNUM3var1toNUM2->(var0->NUM3 + var1->NUM2) +
		var1toNUM3var0toNUM2->(var1->NUM3 + var0->NUM2) +
		var0toNUM0var1toNUM0var2ton1->(var0->NUM0 + var1->NUM0 + var2->n1) +
		var0toNUM2->(var0->NUM2) +
		var0toNUM0var2ton1var1toNUM2->(var0->NUM0 + var2->n1 + var1->NUM2) +
		var1toNUM0var0toNUM2var2ton1->(var1->NUM0 + var0->NUM2 + var2->n1) +
		var0toNUM1var1toNUM1var2ton1->(var0->NUM1 + var1->NUM1 + var2->n1) +
		var1toNUM0var0toNUM1var2ton2->(var1->NUM0 + var0->NUM1 + var2->n2) +
		var0toNUM0var1toNUM1var2ton2->(var0->NUM0 + var1->NUM1 + var2->n2) +
		var2ton3var0toNUM0var1toNUM0->(var2->n3 + var0->NUM0 + var1->NUM0) +
		var0toNUM1var1toNUM2->(var0->NUM1 + var1->NUM2) +
		var1toNUM3var0toNUM0->(var1->NUM3 + var0->NUM0) +
		var0toNUM3var1toNUM0->(var0->NUM3 + var1->NUM0) +
		var1toNUM1var0toNUM2->(var1->NUM1 + var0->NUM2) +
		var0toNUM3var1toNUM3var2ton2->(var0->NUM3 + var1->NUM3 + var2->n2) +
		var2ton3var0toNUM3var1toNUM2->(var2->n3 + var0->NUM3 + var1->NUM2) +
		var2ton3var1toNUM3var0toNUM2->(var2->n3 + var1->NUM3 + var0->NUM2) +
		var0toNUM0var1toNUM0->(var0->NUM0 + var1->NUM0) +
		var0toNUM0->(var0->NUM0) +
		var0toNUM1var2ton1var1toNUM2->(var0->NUM1 + var2->n1 + var1->NUM2) +
		var1toNUM3var0toNUM0var2ton1->(var1->NUM3 + var0->NUM0 + var2->n1) +
		var0toNUM3var1toNUM0var2ton1->(var0->NUM3 + var1->NUM0 + var2->n1) +
		var1toNUM1var0toNUM2var2ton1->(var1->NUM1 + var0->NUM2 + var2->n1) +
		var0toNUM0var2ton2var1toNUM2->(var0->NUM0 + var2->n2 + var1->NUM2) +
		var1toNUM0var2ton2var0toNUM2->(var1->NUM0 + var2->n2 + var0->NUM2) +
		var0toNUM1var1toNUM1var2ton2->(var0->NUM1 + var1->NUM1 + var2->n2) +
		var2ton3var1toNUM0var0toNUM1->(var2->n3 + var1->NUM0 + var0->NUM1) +
		var2ton3var0toNUM0var1toNUM1->(var2->n3 + var0->NUM0 + var1->NUM1) +
		var2ton3var1toNUM3var0toNUM0->(var2->n3 + var1->NUM3 + var0->NUM0) +
		var0toNUM3var2ton1var1toNUM2->(var0->NUM3 + var2->n1 + var1->NUM2) +
		var1toNUM3var0toNUM2var2ton1->(var1->NUM3 + var0->NUM2 + var2->n1) +
		var2ton2var0toNUM2var1toNUM2->(var2->n2 + var0->NUM2 + var1->NUM2) +
		var1toNUM3var0toNUM1var2ton2->(var1->NUM3 + var0->NUM1 + var2->n2) +
		var0toNUM3var1toNUM1var2ton2->(var0->NUM3 + var1->NUM1 + var2->n2) +
		var2ton3var0toNUM1var1toNUM2->(var2->n3 + var0->NUM1 + var1->NUM2) +
		var2ton3var0toNUM3var1toNUM0->(var2->n3 + var0->NUM3 + var1->NUM0) +
		var2ton3var1toNUM1var0toNUM2->(var2->n3 + var1->NUM1 + var0->NUM2)

	baseName =
		BecomeLeadern1_n1n2n3_NUM1->BecomeLeader +
		BecomeLeadern1_n1n3_NUM2->BecomeLeader +
		BecomeLeadern1_n1n2n3_NUM3->BecomeLeader +
		BecomeLeadern1_n1n2_NUM1->BecomeLeader +
		BecomeLeadern2_n2n3_NUM2->BecomeLeader +
		BecomeLeadern2_n2n3_NUM1->BecomeLeader +
		BecomeLeadern1_n1n2_NUM2->BecomeLeader
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
	Root.children.children in Forall
	Root.children.children.children in Implies
	Root.children.children.children.left in Fluent
	//#(Root.children.children.children.left.flActions) = 1
	Root.children.children.children.right in Implies
	Root.children.children.children.right.left in Fluent
	//#(Root.children.children.children.right.left.flActions) = 1
	Root.children.children.children.right.right in VarLTE
}


one sig NT1 extends NegTrace {} {}

one sig PT1 extends PosTrace {} {}
