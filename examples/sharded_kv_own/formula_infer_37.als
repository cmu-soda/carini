//18
//37
open util/boolean
open util/ordering[Idx] as IdxOrder
open util/ordering[ParamIdx] as ParamIdxOrder

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

sig FlSymAction {
    baseName : BaseName,

    // flToActParamsMap maps fluent-param idxs to action-param idxs.
    // in other words, flToActParamsMap decides which of the action-params will be
    // used for setting a boolean value of the state variable (representing the
    // fluent) in the _hist TLA+ code.
    flToActParamsMap : set(ParamIdx->ParamIdx),

    value : Bool, // init v. term
    mutexFl : Bool
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

    // constraints for improving speed, but sacrifice expressivity
    (mutexFl = True) implies (value = True)
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

    // strong condition for ensuring each fluent category is mutex
    all fl1,fl2 : flActions | (some fl1.baseName & fl2.baseName) implies fl1 = fl2

    // vars is a function
    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)

    // each action must input the same param-types to the fluent
    let flParamTypes = vars.envVarTypes |
        all a : flActions |
            // for each param in the action, its type must match the fluent
            all actIdx : ParamIdx.(a.flToActParamsMap) |
                let flIdx = (a.flToActParamsMap).actIdx |
                    flIdx.flParamTypes = actIdx.(a.baseName.paramTypes)

    // flToActParamsMap is an injective function across all actions
    // this is an overconstraint for improving speed
    all x1,x2,y1,y2 : ParamIdx |
        (x1->y1 in flActions.flToActParamsMap and x2->y2 in flActions.flToActParamsMap) implies (x1->y1 = x2->y2 or (not x1=x2 and not y1=y2))
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

	(Forall+Exists).^(~children) in (Root+Forall+Exists) // prenex normal form
	some Implies // non-degenerate formulas
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

// does this action initiate the fluent?
pred isInitAct[a : Act, e : Env, f : Fluent] {
    // init fluents, both usual and mutex
    (some s : f.flActions |
        s.value = True and a.baseName = s.baseName and (~(f.vars)).(s.flToActParamsMap).(a.params) in e.maps)
    or
    // mutex term fluents
    (some s : f.flActions |
        s.mutexFl = True and s.value = False and a.baseName = s.baseName and (~(f.vars)).(s.flToActParamsMap).(a.params) not in e.maps)
}

// does this action terminate the fluent?
pred isTermAct[a : Act, e : Env, f : Fluent] {
    // term fluents, both usual and mutex
    (some s : f.flActions |
        s.value = False and a.baseName = s.baseName and (~(f.vars)).(s.flToActParamsMap).(a.params) in e.maps)
    or
    // mutex init fluents
    (some s : f.flActions |
        s.mutexFl = True and s.value = True and a.baseName = s.baseName and (~(f.vars)).(s.flToActParamsMap).(a.params) not in e.maps)
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

abstract sig PosTrace extends Trace {} {}
abstract sig NegTrace extends Trace {} {}
one sig EmptyTrace extends Trace {} {
	 no path
}


fun mutInitFluents : set FlSymAction {
	 { a : FlSymAction | a.mutexFl = True }
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
	softno mutInitFluents // fewer mutex fluents
	softno partialFluents // fewer partial fluents
	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals
	minsome flActions // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent.vars // minimize the # of params for each fluent
}
for 8 Formula, 4 FlSymAction

one sig P0, P1, P2, P3 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = P0->P1 + P1->P2 + P2->P3
	all f : Fluent | (f.vars.Var = P0) or (f.vars.Var = P0+P1) or (f.vars.Var = P0+P1+P2) or (f.vars.Var = P0+P1+P2+P3)
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
one sig RecvTransferMsgN1K1V1 extends Act {} {
	params = (P0->N1 + P1->K1 + P2->V1)
}
one sig RecvTransferMsgN2K2V1 extends Act {} {
	params = (P0->N2 + P1->K2 + P2->V1)
}
one sig RecvTransferMsgN1K2V1 extends Act {} {
	params = (P0->N1 + P1->K2 + P2->V1)
}
one sig RecvTransferMsgN2K1V1 extends Act {} {
	params = (P0->N2 + P1->K1 + P2->V1)
}
one sig RecvTransferMsgN1K1V2 extends Act {} {
	params = (P0->N1 + P1->K1 + P2->V2)
}

one sig Reshard extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3
	paramTypes = P0->Key + P1->Value + P2->Node + P3->Node
}
one sig ReshardK1V2N2N1 extends Act {} {
	params = (P0->K1 + P1->V2 + P2->N2 + P3->N1)
}
one sig ReshardK1V1N1N1 extends Act {} {
	params = (P0->K1 + P1->V1 + P2->N1 + P3->N1)
}
one sig ReshardK2V1N1N2 extends Act {} {
	params = (P0->K2 + P1->V1 + P2->N1 + P3->N2)
}
one sig ReshardK1V1N2N2 extends Act {} {
	params = (P0->K1 + P1->V1 + P2->N2 + P3->N2)
}
one sig ReshardK1V1N1N2 extends Act {} {
	params = (P0->K1 + P1->V1 + P2->N1 + P3->N2)
}
one sig ReshardK2V1N1N1 extends Act {} {
	params = (P0->K2 + P1->V1 + P2->N1 + P3->N1)
}

one sig Own extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Node + P1->Key
}
one sig OwnN1K2 extends Act {} {
	params = (P0->N1 + P1->K2)
}
one sig OwnN1K1 extends Act {} {
	params = (P0->N1 + P1->K1)
}
one sig OwnN2K2 extends Act {} {
	params = (P0->N2 + P1->K2)
}


one sig T0, T1, T2, T3, T4, T5 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5
	RecvTransferMsg in FlSymAction.baseName // the final base name in the neg trace must appear in the sep formula
}


fun envVarTypes : set(Var->Sort) {
	var3->Node + var2->Node + var1->Node + var0->Key
}


one sig var3, var2, var1, var0 extends Var {} {}


one sig var0toK1 extends Env {} {}
one sig var2toN2var1toN2var0toK2var3toN2 extends Env {} {}
one sig var0toK2 extends Env {} {}
one sig var2toN2var1toN2var3toN1var0toK2 extends Env {} {}
one sig var1toN2var2toN1var0toK2var3toN2 extends Env {} {}
one sig var2toN2var1toN1var0toK2var3toN2 extends Env {} {}
one sig var2toN2var0toK1var1toN2var3toN2 extends Env {} {}
one sig var0toK1var1toN1var2toN1 extends Env {} {}
one sig var1toN1var2toN1var0toK2 extends Env {} {}
one sig var0toK1var1toN2var2toN1 extends Env {} {}
one sig var2toN2var0toK1var1toN1 extends Env {} {}
one sig var1toN2var2toN1var0toK2 extends Env {} {}
one sig var2toN2var1toN1var0toK2 extends Env {} {}
one sig var2toN2var0toK1var1toN2 extends Env {} {}
one sig var2toN2var1toN2var0toK2 extends Env {} {}
one sig var1toN2var3toN1var2toN1var0toK2 extends Env {} {}
one sig var2toN2var1toN1var3toN1var0toK2 extends Env {} {}
one sig var2toN2var0toK1var1toN2var3toN1 extends Env {} {}
one sig var1toN1var2toN1var0toK2var3toN2 extends Env {} {}
one sig var0toK1var1toN2var2toN1var3toN2 extends Env {} {}
one sig var2toN2var0toK1var1toN1var3toN2 extends Env {} {}
one sig var0toK1var1toN1 extends Env {} {}
one sig var1toN1var3toN1var2toN1var0toK2 extends Env {} {}
one sig var0toK1var1toN2var3toN1var2toN1 extends Env {} {}
one sig var2toN2var0toK1var1toN1var3toN1 extends Env {} {}
one sig var0toK1var1toN1var2toN1var3toN2 extends Env {} {}
one sig var1toN1var0toK2 extends Env {} {}
one sig var0toK1var1toN2 extends Env {} {}
one sig var1toN2var0toK2 extends Env {} {}
one sig var0toK1var1toN1var3toN1var2toN1 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT34->T4) + (PT28->T4) + (PT25->T4) + (PT31->T5) + (PT35->T4) + (PT27->T3) + (PT32->T4) + (PT22->T3) + (PT37->T5) + (PT30->T5) + (PT36->T4) + (PT33->T3) + (PT26->T4) + (PT1->T5) + (PT18->T2) + (NT1->T5)

	path = (PT34 -> (T0->OwnN1K1 + T1->ReshardK1V1N1N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN2K1V1 + T4->RecvTransferMsgN1K1V1)) +
		(PT28 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN1K1V1 + T3->RecvTransferMsgN2K1V1 + T4->OwnN1K1)) +
		(PT25 -> (T0->ReshardK1V1N1N1 + T1->ReshardK2V1N1N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN2K1V1)) +
		(PT31 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N2N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN2K1V1 + T5->OwnN1K2)) +
		(PT35 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN2K1V1 + T3->OwnN1K1 + T4->RecvTransferMsgN1K2V1)) +
		(PT27 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN1K2V1 + T3->OwnN1K2)) +
		(PT32 -> (T0->ReshardK2V1N1N1 + T1->ReshardK2V1N1N2 + T2->RecvTransferMsgN2K2V1 + T3->RecvTransferMsgN1K2V1 + T4->OwnN1K2)) +
		(PT22 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN2K1V1 + T3->RecvTransferMsgN1K1V1)) +
		(PT37 -> (T0->ReshardK1V2N2N1 + T1->OwnN2K2 + T2->ReshardK2V1N1N1 + T3->ReshardK2V1N1N2 + T4->RecvTransferMsgN1K2V1 + T5->RecvTransferMsgN2K2V1)) +
		(PT30 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N2N1 + T2->ReshardK2V1N1N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN2K2V1 + T5->OwnN1K2)) +
		(PT36 -> (T0->OwnN1K1 + T1->ReshardK1V1N1N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN2K1V1)) +
		(PT33 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N1N2 + T2->RecvTransferMsgN1K1V1 + T3->RecvTransferMsgN2K1V1)) +
		(PT26 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V2N2N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN2K1V1 + T4->RecvTransferMsgN1K1V2)) +
		(PT1 -> (T0->OwnN1K1 + T1->ReshardK1V1N1N1 + T2->RecvTransferMsgN1K1V1 + T3->ReshardK1V1N1N2 + T4->RecvTransferMsgN2K1V1 + T5->ReshardK1V1N1N1)) +
		(PT18 -> (T0->ReshardK1V2N2N1 + T1->ReshardK2V1N1N2 + T2->RecvTransferMsgN1K1V2)) +
		(NT1 -> (T0->OwnN1K1 + T1->ReshardK1V1N1N1 + T2->RecvTransferMsgN1K1V1 + T3->ReshardK1V1N1N2 + T4->RecvTransferMsgN1K1V1 + T5->RecvTransferMsgN2K1V1))

	maps = var0toK1->(var0->K1) +
		var2toN2var1toN2var0toK2var3toN2->(var2->N2 + var1->N2 + var0->K2 + var3->N2) +
		var0toK2->(var0->K2) +
		var2toN2var1toN2var3toN1var0toK2->(var2->N2 + var1->N2 + var3->N1 + var0->K2) +
		var1toN2var2toN1var0toK2var3toN2->(var1->N2 + var2->N1 + var0->K2 + var3->N2) +
		var2toN2var1toN1var0toK2var3toN2->(var2->N2 + var1->N1 + var0->K2 + var3->N2) +
		var2toN2var0toK1var1toN2var3toN2->(var2->N2 + var0->K1 + var1->N2 + var3->N2) +
		var0toK1var1toN1var2toN1->(var0->K1 + var1->N1 + var2->N1) +
		var1toN1var2toN1var0toK2->(var1->N1 + var2->N1 + var0->K2) +
		var0toK1var1toN2var2toN1->(var0->K1 + var1->N2 + var2->N1) +
		var2toN2var0toK1var1toN1->(var2->N2 + var0->K1 + var1->N1) +
		var1toN2var2toN1var0toK2->(var1->N2 + var2->N1 + var0->K2) +
		var2toN2var1toN1var0toK2->(var2->N2 + var1->N1 + var0->K2) +
		var2toN2var0toK1var1toN2->(var2->N2 + var0->K1 + var1->N2) +
		var2toN2var1toN2var0toK2->(var2->N2 + var1->N2 + var0->K2) +
		var1toN2var3toN1var2toN1var0toK2->(var1->N2 + var3->N1 + var2->N1 + var0->K2) +
		var2toN2var1toN1var3toN1var0toK2->(var2->N2 + var1->N1 + var3->N1 + var0->K2) +
		var2toN2var0toK1var1toN2var3toN1->(var2->N2 + var0->K1 + var1->N2 + var3->N1) +
		var1toN1var2toN1var0toK2var3toN2->(var1->N1 + var2->N1 + var0->K2 + var3->N2) +
		var0toK1var1toN2var2toN1var3toN2->(var0->K1 + var1->N2 + var2->N1 + var3->N2) +
		var2toN2var0toK1var1toN1var3toN2->(var2->N2 + var0->K1 + var1->N1 + var3->N2) +
		var0toK1var1toN1->(var0->K1 + var1->N1) +
		var1toN1var3toN1var2toN1var0toK2->(var1->N1 + var3->N1 + var2->N1 + var0->K2) +
		var0toK1var1toN2var3toN1var2toN1->(var0->K1 + var1->N2 + var3->N1 + var2->N1) +
		var2toN2var0toK1var1toN1var3toN1->(var2->N2 + var0->K1 + var1->N1 + var3->N1) +
		var0toK1var1toN1var2toN1var3toN2->(var0->K1 + var1->N1 + var2->N1 + var3->N2) +
		var1toN1var0toK2->(var1->N1 + var0->K2) +
		var0toK1var1toN2->(var0->K1 + var1->N2) +
		var1toN2var0toK2->(var1->N2 + var0->K2) +
		var0toK1var1toN1var3toN1var2toN1->(var0->K1 + var1->N1 + var3->N1 + var2->N1)

	baseName = OwnN1K1->Own +
		ReshardK1V2N2N1->Reshard +
		RecvTransferMsgN1K1V1->RecvTransferMsg +
		RecvTransferMsgN1K2V1->RecvTransferMsg +
		RecvTransferMsgN1K1V2->RecvTransferMsg +
		ReshardK1V1N1N1->Reshard +
		ReshardK2V1N1N2->Reshard +
		ReshardK1V1N1N2->Reshard +
		RecvTransferMsgN2K2V1->RecvTransferMsg +
		ReshardK1V1N2N2->Reshard +
		ReshardK2V1N1N1->Reshard +
		OwnN2K2->Own +
		RecvTransferMsgN2K1V1->RecvTransferMsg +
		OwnN1K2->Own
}


fact {
	#(Forall + Exists) <= 4 // allow only 4 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT34 extends PosTrace {} {}
one sig PT28 extends PosTrace {} {}
one sig PT25 extends PosTrace {} {}
one sig PT31 extends PosTrace {} {}
one sig PT35 extends PosTrace {} {}
one sig PT27 extends PosTrace {} {}
one sig PT32 extends PosTrace {} {}
one sig PT22 extends PosTrace {} {}
one sig PT37 extends PosTrace {} {}
one sig PT30 extends PosTrace {} {}
one sig PT36 extends PosTrace {} {}
one sig PT33 extends PosTrace {} {}
one sig PT26 extends PosTrace {} {}
one sig PT1 extends PosTrace {} {}
one sig PT18 extends PosTrace {} {}
