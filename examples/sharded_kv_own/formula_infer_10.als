//45
//10
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
for 8 Formula, 5 FlSymAction

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
one sig RecvTransferMsgN2K2V1 extends Act {} {
	params = (P0->N2 + P1->K2 + P2->V1)
}
one sig RecvTransferMsgN1K2V1 extends Act {} {
	params = (P0->N1 + P1->K2 + P2->V1)
}
one sig RecvTransferMsgN2K1V2 extends Act {} {
	params = (P0->N2 + P1->K1 + P2->V2)
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
one sig ReshardK1V2N1N2 extends Act {} {
	params = (P0->K1 + P1->V2 + P2->N1 + P3->N2)
}
one sig ReshardK1V2N2N1 extends Act {} {
	params = (P0->K1 + P1->V2 + P2->N2 + P3->N1)
}
one sig ReshardK1V1N1N1 extends Act {} {
	params = (P0->K1 + P1->V1 + P2->N1 + P3->N1)
}
one sig ReshardK2V2N1N1 extends Act {} {
	params = (P0->K2 + P1->V2 + P2->N1 + P3->N1)
}
one sig ReshardK2V1N1N2 extends Act {} {
	params = (P0->K2 + P1->V1 + P2->N1 + P3->N2)
}
one sig ReshardK1V1N2N2 extends Act {} {
	params = (P0->K1 + P1->V1 + P2->N2 + P3->N2)
}
one sig ReshardK1V2N1N1 extends Act {} {
	params = (P0->K1 + P1->V2 + P2->N1 + P3->N1)
}
one sig ReshardK1V2N2N2 extends Act {} {
	params = (P0->K1 + P1->V2 + P2->N2 + P3->N2)
}
one sig ReshardK1V1N1N2 extends Act {} {
	params = (P0->K1 + P1->V1 + P2->N1 + P3->N2)
}
one sig ReshardK2V2N1N2 extends Act {} {
	params = (P0->K2 + P1->V2 + P2->N1 + P3->N2)
}
one sig ReshardK2V1N2N1 extends Act {} {
	params = (P0->K2 + P1->V1 + P2->N2 + P3->N1)
}
one sig ReshardK2V1N1N1 extends Act {} {
	params = (P0->K2 + P1->V1 + P2->N1 + P3->N1)
}
one sig ReshardK1V1N2N1 extends Act {} {
	params = (P0->K1 + P1->V1 + P2->N2 + P3->N1)
}
one sig ReshardK2V2N2N1 extends Act {} {
	params = (P0->K2 + P1->V2 + P2->N2 + P3->N1)
}
one sig ReshardK2V1N2N2 extends Act {} {
	params = (P0->K2 + P1->V1 + P2->N2 + P3->N2)
}

one sig Own extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Node + P1->Key
}
one sig OwnN2K1 extends Act {} {
	params = (P0->N2 + P1->K1)
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

one sig Put extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Node + P1->Key + P2->Value
}
one sig PutN1K1V1 extends Act {} {
	params = (P0->N1 + P1->K1 + P2->V1)
}
one sig PutN2K2V1 extends Act {} {
	params = (P0->N2 + P1->K2 + P2->V1)
}
one sig PutN1K2V1 extends Act {} {
	params = (P0->N1 + P1->K2 + P2->V1)
}
one sig PutN2K1V2 extends Act {} {
	params = (P0->N2 + P1->K1 + P2->V2)
}
one sig PutN2K1V1 extends Act {} {
	params = (P0->N2 + P1->K1 + P2->V1)
}
one sig PutN1K1V2 extends Act {} {
	params = (P0->N1 + P1->K1 + P2->V2)
}


one sig T0, T1, T2, T3, T4, T5, T6, T7 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6 + T6->T7
	RecvTransferMsg in FlSymAction.baseName // the final base name in the neg trace must appear in the sep formula
}


fun envVarTypes : set(Var->Sort) {
	var2->Node + var1->Value + var0->Key
}


one sig var2, var1, var0 extends Var {} {}


one sig var1toV1var2toN1var0toK2 extends Env {} {}
one sig var0toK1var1toV2var2toN1 extends Env {} {}
one sig var2toN2var1toV1var0toK1 extends Env {} {}
one sig var0toK1 extends Env {} {}
one sig var1toV1var0toK1var2toN1 extends Env {} {}
one sig var0toK2 extends Env {} {}
one sig var1toV2var2toN1var0toK2 extends Env {} {}
one sig var2toN2var1toV1var0toK2 extends Env {} {}
one sig var2toN2var0toK1var1toV2 extends Env {} {}
one sig var1toV2var0toK2 extends Env {} {}
one sig var1toV1var0toK1 extends Env {} {}
one sig var1toV1var0toK2 extends Env {} {}
one sig var0toK1var1toV2 extends Env {} {}
one sig var2toN2var1toV2var0toK2 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT123->T7) + (PT99->T6) + (PT89->T5) + (PT62->T4) + (PT128->T4) + (PT95->T6) + (PT90->T5) + (PT96->T5) + (PT71->T5) + (PT77->T5) + (PT101->T6) + (PT121->T5) + (PT93->T5) + (PT87->T5) + (PT82->T6) + (PT81->T4) + (PT94->T7) + (PT119->T5) + (PT110->T6) + (PT80->T6) + (PT61->T4) + (PT72->T3) + (PT127->T4) + (PT98->T5) + (PT97->T5) + (PT122->T5) + (PT116->T5) + (PT73->T3) + (PT120->T6) + (PT54->T2) + (PT83->T5) + (PT75->T5) + (PT118->T6) + (PT88->T5) + (PT115->T6) + (PT64->T4) + (PT92->T5) + (PT124->T5) + (PT126->T4) + (PT91->T4) + (PT104->T5) + (PT105->T5) + (PT103->T5) + (PT85->T4) + (PT100->T4) + (PT86->T5) + (PT106->T3) + (PT65->T3) + (PT114->T5) + (PT102->T6) + (PT111->T4) + (PT108->T4) + (PT84->T5) + (PT107->T5) + (PT109->T5) + (PT125->T5) + (PT66->T4) + (PT74->T6) + (PT1->T6) + (PT67->T4) + (PT76->T4) + (PT112->T5) + (PT117->T4) + (NT1->T6)

	path = (PT123 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V1N1N1 + T2->ReshardK1V1N2N2 + T3->ReshardK2V1N1N2 + T4->RecvTransferMsgN1K1V1 + T5->RecvTransferMsgN2K1V1 + T6->RecvTransferMsgN2K2V1 + T7->RecvTransferMsgN1K2V1)) +
		(PT99 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V2N2N1 + T2->RecvTransferMsgN1K2V1 + T3->PutN1K2V1 + T4->ReshardK2V1N1N2 + T5->RecvTransferMsgN2K2V1 + T6->RecvTransferMsgN1K1V2)) +
		(PT89 -> (T0->ReshardK1V1N1N1 + T1->ReshardK2V2N1N1 + T2->RecvTransferMsgN1K1V1 + T3->PutN1K1V1 + T4->ReshardK1V1N1N2 + T5->RecvTransferMsgN1K2V2)) +
		(PT62 -> (T0->ReshardK1V2N2N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN2K1V1 + T3->RecvTransferMsgN1K1V2 + T4->OwnN1K2)) +
		(PT128 -> (T0->OwnN1K1 + T1->ReshardK1V1N1N1 + T2->ReshardK1V1N1N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN2K1V1)) +
		(PT95 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N2N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN2K1V1 + T4->RecvTransferMsgN1K1V2 + T5->PutN1K1V1 + T6->RecvTransferMsgN1K1V1)) +
		(PT90 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN1K1V1 + T3->RecvTransferMsgN2K1V1 + T4->PutN2K1V1 + T5->PutN1K1V1)) +
		(PT96 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V2N1N1 + T2->ReshardK1V1N1N2 + T3->ReshardK2V1N1N2 + T4->RecvTransferMsgN1K2V1 + T5->RecvTransferMsgN1K1V2)) +
		(PT71 -> (T0->ReshardK2V2N1N1 + T1->OwnN1K1 + T2->ReshardK1V1N1N1 + T3->ReshardK1V2N2N2 + T4->RecvTransferMsgN1K1V1 + T5->RecvTransferMsgN2K1V2)) +
		(PT77 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N1N2 + T2->OwnN1K2 + T3->PutN1K2V1 + T4->RecvTransferMsgN1K1V1 + T5->RecvTransferMsgN2K1V1)) +
		(PT101 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N1N1 + T2->ReshardK1V1N1N2 + T3->RecvTransferMsgN1K1V2 + T4->PutN1K1V1 + T5->RecvTransferMsgN1K1V1 + T6->RecvTransferMsgN2K1V1)) +
		(PT121 -> (T0->ReshardK2V1N1N1 + T1->ReshardK2V1N1N2 + T2->RecvTransferMsgN1K2V1 + T3->PutN1K2V1 + T4->ReshardK2V1N2N1 + T5->RecvTransferMsgN2K2V1)) +
		(PT93 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N2N2 + T2->RecvTransferMsgN1K1V1 + T3->RecvTransferMsgN2K1V2 + T4->PutN2K1V1 + T5->PutN1K1V2)) +
		(PT87 -> (T0->ReshardK2V2N1N1 + T1->ReshardK1V1N1N1 + T2->RecvTransferMsgN1K1V1 + T3->PutN1K1V1 + T4->ReshardK2V1N1N2 + T5->RecvTransferMsgN1K2V2)) +
		(PT82 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N2N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN2K1V1 + T5->PutN1K1V1 + T6->RecvTransferMsgN1K1V2)) +
		(PT81 -> (T0->ReshardK2V1N1N1 + T1->ReshardK2V1N1N2 + T2->OwnN1K1 + T3->PutN1K1V1 + T4->RecvTransferMsgN1K2V1)) +
		(PT94 -> (T0->ReshardK1V1N1N1 + T1->ReshardK2V1N1N1 + T2->ReshardK1V2N2N1 + T3->ReshardK1V1N2N2 + T4->RecvTransferMsgN1K1V2 + T5->PutN1K1V1 + T6->RecvTransferMsgN2K1V1 + T7->RecvTransferMsgN1K1V1)) +
		(PT119 -> (T0->ReshardK1V1N1N1 + T1->ReshardK2V1N1N1 + T2->ReshardK1V1N2N2 + T3->ReshardK2V1N1N2 + T4->RecvTransferMsgN1K1V1 + T5->RecvTransferMsgN2K1V1)) +
		(PT110 -> (T0->ReshardK1V2N2N1 + T1->ReshardK1V1N1N1 + T2->RecvTransferMsgN1K1V1 + T3->PutN1K1V1 + T4->ReshardK1V1N2N1 + T5->ReshardK2V1N2N2 + T6->RecvTransferMsgN2K2V1)) +
		(PT80 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N2N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN1K1V1 + T4->PutN1K1V1 + T5->RecvTransferMsgN2K1V1 + T6->RecvTransferMsgN1K1V2)) +
		(PT61 -> (T0->ReshardK2V1N1N1 + T1->ReshardK2V1N1N2 + T2->RecvTransferMsgN1K2V1 + T3->RecvTransferMsgN2K2V1 + T4->OwnN1K1)) +
		(PT72 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N1N2 + T2->RecvTransferMsgN1K1V1 + T3->PutN1K1V1)) +
		(PT127 -> (T0->OwnN1K1 + T1->ReshardK1V1N2N1 + T2->ReshardK1V1N1N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN2K1V1)) +
		(PT98 -> (T0->ReshardK1V1N1N1 + T1->RecvTransferMsgN1K1V1 + T2->OwnN2K2 + T3->PutN2K2V1 + T4->ReshardK1V1N2N2 + T5->RecvTransferMsgN2K1V1)) +
		(PT97 -> (T0->ReshardK1V1N1N1 + T1->RecvTransferMsgN1K1V1 + T2->OwnN2K2 + T3->PutN2K2V1 + T4->ReshardK2V1N2N2 + T5->RecvTransferMsgN2K2V1)) +
		(PT122 -> (T0->ReshardK2V1N1N1 + T1->ReshardK2V1N1N2 + T2->RecvTransferMsgN1K2V1 + T3->PutN1K2V1 + T4->ReshardK2V2N2N1 + T5->RecvTransferMsgN2K2V1)) +
		(PT116 -> (T0->OwnN1K1 + T1->PutN1K1V1 + T2->ReshardK1V1N1N1 + T3->ReshardK1V1N2N2 + T4->RecvTransferMsgN1K1V1 + T5->RecvTransferMsgN2K1V1)) +
		(PT73 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V1N1N2 + T2->RecvTransferMsgN1K2V1 + T3->PutN1K2V1)) +
		(PT120 -> (T0->ReshardK2V1N1N1 + T1->ReshardK2V1N1N2 + T2->RecvTransferMsgN1K2V1 + T3->ReshardK2V1N2N1 + T4->RecvTransferMsgN2K2V1 + T5->PutN1K2V1 + T6->RecvTransferMsgN1K2V1)) +
		(PT54 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N1N2 + T2->RecvTransferMsgN1K1V1)) +
		(PT83 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V1N1N1 + T2->ReshardK1V1N1N2 + T3->RecvTransferMsgN1K1V1 + T4->PutN1K1V1 + T5->RecvTransferMsgN1K2V1)) +
		(PT75 -> (T0->ReshardK1V1N1N1 + T1->OwnN1K2 + T2->ReshardK2V1N1N1 + T3->ReshardK2V1N1N2 + T4->RecvTransferMsgN1K2V1 + T5->RecvTransferMsgN2K2V1)) +
		(PT118 -> (T0->ReshardK1V1N1N1 + T1->RecvTransferMsgN1K1V1 + T2->PutN1K1V1 + T3->ReshardK2V1N1N1 + T4->ReshardK1V1N1N2 + T5->RecvTransferMsgN2K1V1 + T6->RecvTransferMsgN1K2V1)) +
		(PT88 -> (T0->ReshardK1V1N1N1 + T1->ReshardK2V1N1N1 + T2->RecvTransferMsgN1K1V1 + T3->PutN1K1V1 + T4->ReshardK2V1N1N2 + T5->RecvTransferMsgN1K2V1)) +
		(PT115 -> (T0->ReshardK1V1N1N1 + T1->ReshardK2V1N1N1 + T2->RecvTransferMsgN1K1V1 + T3->PutN1K1V1 + T4->ReshardK1V1N1N2 + T5->RecvTransferMsgN2K1V1 + T6->RecvTransferMsgN1K2V1)) +
		(PT64 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN1K1V1 + T3->RecvTransferMsgN2K1V1 + T4->PutN1K1V1)) +
		(PT92 -> (T0->ReshardK1V1N1N1 + T1->RecvTransferMsgN1K1V1 + T2->PutN1K1V1 + T3->ReshardK2V1N1N1 + T4->ReshardK2V2N1N2 + T5->RecvTransferMsgN1K2V1)) +
		(PT124 -> (T0->ReshardK1V1N1N1 + T1->OwnN1K2 + T2->PutN1K2V1 + T3->ReshardK1V1N1N2 + T4->RecvTransferMsgN2K1V1 + T5->RecvTransferMsgN1K1V1)) +
		(PT126 -> (T0->OwnN1K1 + T1->ReshardK1V1N1N1 + T2->ReshardK1V2N1N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN2K1V2)) +
		(PT91 -> (T0->ReshardK1V1N1N1 + T1->RecvTransferMsgN1K1V1 + T2->PutN1K1V1 + T3->ReshardK1V1N2N2 + T4->RecvTransferMsgN2K1V1)) +
		(PT104 -> (T0->ReshardK1V2N2N1 + T1->ReshardK1V1N1N1 + T2->ReshardK1V1N1N2 + T3->RecvTransferMsgN1K1V1 + T4->PutN1K1V1 + T5->RecvTransferMsgN1K1V2)) +
		(PT105 -> (T0->ReshardK1V2N1N1 + T1->ReshardK1V1N1N1 + T2->ReshardK1V1N1N2 + T3->RecvTransferMsgN1K1V1 + T4->PutN1K1V1 + T5->RecvTransferMsgN1K1V2)) +
		(PT103 -> (T0->ReshardK1V2N1N1 + T1->ReshardK1V1N1N2 + T2->RecvTransferMsgN1K1V2 + T3->PutN1K1V1 + T4->ReshardK1V1N1N1 + T5->RecvTransferMsgN1K1V1)) +
		(PT85 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN1K1V1 + T3->RecvTransferMsgN2K1V1 + T4->PutN1K1V2)) +
		(PT100 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N2N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN1K1V2)) +
		(PT86 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN1K1V1 + T3->RecvTransferMsgN2K1V1 + T4->OwnN1K2 + T5->PutN1K2V1)) +
		(PT106 -> (T0->ReshardK1V1N2N1 + T1->ReshardK1V2N1N2 + T2->ReshardK2V2N2N1 + T3->RecvTransferMsgN2K1V2)) +
		(PT65 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N1N2 + T2->RecvTransferMsgN2K1V1 + T3->RecvTransferMsgN1K1V1)) +
		(PT114 -> (T0->ReshardK1V1N1N1 + T1->OwnN2K2 + T2->PutN2K2V1 + T3->ReshardK1V1N2N2 + T4->RecvTransferMsgN1K1V1 + T5->RecvTransferMsgN2K1V1)) +
		(PT102 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V2N2N1 + T2->RecvTransferMsgN1K1V2 + T3->PutN1K1V1 + T4->ReshardK1V1N1N2 + T5->RecvTransferMsgN1K1V1 + T6->RecvTransferMsgN2K1V1)) +
		(PT111 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N1N2 + T2->OwnN1K2 + T3->ReshardK2V1N1N2 + T4->RecvTransferMsgN1K1V1)) +
		(PT108 -> (T0->OwnN1K1 + T1->PutN1K1V1 + T2->ReshardK1V1N1N1 + T3->ReshardK1V1N1N2 + T4->RecvTransferMsgN1K1V1)) +
		(PT84 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N2N2 + T2->OwnN1K2 + T3->PutN1K2V1 + T4->RecvTransferMsgN1K1V1 + T5->RecvTransferMsgN2K1V1)) +
		(PT107 -> (T0->ReshardK2V2N1N1 + T1->OwnN2K1 + T2->PutN2K1V1 + T3->ReshardK2V1N1N2 + T4->RecvTransferMsgN2K2V1 + T5->RecvTransferMsgN1K2V2)) +
		(PT109 -> (T0->OwnN1K1 + T1->ReshardK1V1N1N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN1K1V1 + T4->RecvTransferMsgN2K1V1 + T5->PutN1K1V1)) +
		(PT125 -> (T0->ReshardK2V2N1N1 + T1->OwnN1K1 + T2->PutN1K1V1 + T3->ReshardK1V1N1N2 + T4->RecvTransferMsgN2K1V1 + T5->RecvTransferMsgN1K2V2)) +
		(PT66 -> (T0->ReshardK1V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN2K1V1 + T3->RecvTransferMsgN1K1V1 + T4->OwnN1K2)) +
		(PT74 -> (T0->ReshardK1V2N2N1 + T1->ReshardK2V1N1N1 + T2->ReshardK1V1N2N2 + T3->RecvTransferMsgN2K1V1 + T4->RecvTransferMsgN1K1V2 + T5->PutN1K1V1 + T6->RecvTransferMsgN1K2V1)) +
		(PT1 -> (T0->OwnN1K1 + T1->PutN1K1V1 + T2->ReshardK1V1N1N1 + T3->RecvTransferMsgN1K1V1 + T4->ReshardK1V1N1N2 + T5->RecvTransferMsgN2K1V1 + T6->ReshardK1V1N1N1)) +
		(PT67 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN2K1V1 + T3->RecvTransferMsgN1K2V1 + T4->PutN2K1V1)) +
		(PT76 -> (T0->ReshardK2V1N1N1 + T1->ReshardK1V1N2N2 + T2->RecvTransferMsgN2K1V1 + T3->RecvTransferMsgN1K2V1 + T4->PutN2K1V2)) +
		(PT112 -> (T0->ReshardK2V1N1N1 + T1->RecvTransferMsgN1K2V1 + T2->PutN1K2V1 + T3->ReshardK1V1N1N1 + T4->ReshardK1V1N1N2 + T5->RecvTransferMsgN1K1V1)) +
		(PT117 -> (T0->ReshardK2V1N1N1 + T1->ReshardK2V2N1N1 + T2->RecvTransferMsgN1K2V1 + T3->PutN1K2V1 + T4->OwnN1K1)) +
		(NT1 -> (T0->OwnN1K1 + T1->PutN1K1V1 + T2->ReshardK1V1N1N1 + T3->RecvTransferMsgN1K1V1 + T4->ReshardK1V1N1N2 + T5->RecvTransferMsgN1K1V1 + T6->RecvTransferMsgN2K1V1))

	maps = var1toV1var2toN1var0toK2->(var1->V1 + var2->N1 + var0->K2) +
		var0toK1var1toV2var2toN1->(var0->K1 + var1->V2 + var2->N1) +
		var2toN2var1toV1var0toK1->(var2->N2 + var1->V1 + var0->K1) +
		var0toK1->(var0->K1) +
		var1toV1var0toK1var2toN1->(var1->V1 + var0->K1 + var2->N1) +
		var0toK2->(var0->K2) +
		var1toV2var2toN1var0toK2->(var1->V2 + var2->N1 + var0->K2) +
		var2toN2var1toV1var0toK2->(var2->N2 + var1->V1 + var0->K2) +
		var2toN2var0toK1var1toV2->(var2->N2 + var0->K1 + var1->V2) +
		var1toV2var0toK2->(var1->V2 + var0->K2) +
		var1toV1var0toK1->(var1->V1 + var0->K1) +
		var1toV1var0toK2->(var1->V1 + var0->K2) +
		var0toK1var1toV2->(var0->K1 + var1->V2) +
		var2toN2var1toV2var0toK2->(var2->N2 + var1->V2 + var0->K2)

	baseName = OwnN1K1->Own +
		ReshardK1V2N1N2->Reshard +
		ReshardK1V2N2N1->Reshard +
		ReshardK1V2N2N2->Reshard +
		ReshardK1V2N1N1->Reshard +
		RecvTransferMsgN1K1V1->RecvTransferMsg +
		RecvTransferMsgN1K2V1->RecvTransferMsg +
		RecvTransferMsgN1K1V2->RecvTransferMsg +
		RecvTransferMsgN1K2V2->RecvTransferMsg +
		ReshardK1V1N1N1->Reshard +
		ReshardK1V1N1N2->Reshard +
		ReshardK1V1N2N1->Reshard +
		ReshardK1V1N2N2->Reshard +
		OwnN2K2->Own +
		OwnN2K1->Own +
		OwnN1K2->Own +
		ReshardK2V2N1N1->Reshard +
		PutN2K1V1->Put +
		ReshardK2V2N1N2->Reshard +
		ReshardK2V2N2N1->Reshard +
		PutN2K2V1->Put +
		PutN2K1V2->Put +
		ReshardK2V1N1N2->Reshard +
		ReshardK2V1N2N1->Reshard +
		PutN1K2V1->Put +
		PutN1K1V2->Put +
		ReshardK2V1N2N2->Reshard +
		RecvTransferMsgN2K2V1->RecvTransferMsg +
		RecvTransferMsgN2K1V2->RecvTransferMsg +
		ReshardK2V1N1N1->Reshard +
		PutN1K1V1->Put +
		RecvTransferMsgN2K1V1->RecvTransferMsg
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT123 extends PosTrace {} {}
one sig PT99 extends PosTrace {} {}
one sig PT89 extends PosTrace {} {}
one sig PT62 extends PosTrace {} {}
one sig PT128 extends PosTrace {} {}
one sig PT95 extends PosTrace {} {}
one sig PT90 extends PosTrace {} {}
one sig PT96 extends PosTrace {} {}
one sig PT71 extends PosTrace {} {}
one sig PT77 extends PosTrace {} {}
one sig PT101 extends PosTrace {} {}
one sig PT121 extends PosTrace {} {}
one sig PT93 extends PosTrace {} {}
one sig PT87 extends PosTrace {} {}
one sig PT82 extends PosTrace {} {}
one sig PT81 extends PosTrace {} {}
one sig PT94 extends PosTrace {} {}
one sig PT119 extends PosTrace {} {}
one sig PT110 extends PosTrace {} {}
one sig PT80 extends PosTrace {} {}
one sig PT61 extends PosTrace {} {}
one sig PT72 extends PosTrace {} {}
one sig PT127 extends PosTrace {} {}
one sig PT98 extends PosTrace {} {}
one sig PT97 extends PosTrace {} {}
one sig PT122 extends PosTrace {} {}
one sig PT116 extends PosTrace {} {}
one sig PT73 extends PosTrace {} {}
one sig PT120 extends PosTrace {} {}
one sig PT54 extends PosTrace {} {}
one sig PT83 extends PosTrace {} {}
one sig PT75 extends PosTrace {} {}
one sig PT118 extends PosTrace {} {}
one sig PT88 extends PosTrace {} {}
one sig PT115 extends PosTrace {} {}
one sig PT64 extends PosTrace {} {}
one sig PT92 extends PosTrace {} {}
one sig PT124 extends PosTrace {} {}
one sig PT126 extends PosTrace {} {}
one sig PT91 extends PosTrace {} {}
one sig PT104 extends PosTrace {} {}
one sig PT105 extends PosTrace {} {}
one sig PT103 extends PosTrace {} {}
one sig PT85 extends PosTrace {} {}
one sig PT100 extends PosTrace {} {}
one sig PT86 extends PosTrace {} {}
one sig PT106 extends PosTrace {} {}
one sig PT65 extends PosTrace {} {}
one sig PT114 extends PosTrace {} {}
one sig PT102 extends PosTrace {} {}
one sig PT111 extends PosTrace {} {}
one sig PT108 extends PosTrace {} {}
one sig PT84 extends PosTrace {} {}
one sig PT107 extends PosTrace {} {}
one sig PT109 extends PosTrace {} {}
one sig PT125 extends PosTrace {} {}
one sig PT66 extends PosTrace {} {}
one sig PT74 extends PosTrace {} {}
one sig PT1 extends PosTrace {} {}
one sig PT67 extends PosTrace {} {}
one sig PT76 extends PosTrace {} {}
one sig PT112 extends PosTrace {} {}
one sig PT117 extends PosTrace {} {}
