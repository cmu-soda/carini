//214
//15
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
	let containsRel = (none->none) |
		(lhs->rhs) in containsRel
}


one sig a1, a2, v1, v2, c1, c2 extends Atom {}

one sig Value extends Sort {} {
	atoms = v1 + v2
	numericSort = False
}
one sig Address extends Sort {} {
	atoms = a1 + a2
	numericSort = False
}
one sig Core extends Sort {} {
	atoms = c1 + c2
	numericSort = False
}

one sig issue_proc_write_invalid extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Core + P1->Address + P2->Value
}
one sig issue_proc_write_invalidc2a1v2 extends Act {} {
	params = (P0->c2 + P1->a1 + P2->v2)
}
one sig issue_proc_write_invalidc1a1v2 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v2)
}
one sig issue_proc_write_invalidc2a1v1 extends Act {} {
	params = (P0->c2 + P1->a1 + P2->v1)
}
one sig issue_proc_write_invalidc1a1v1 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v1)
}
one sig issue_proc_write_invalidc2a2v1 extends Act {} {
	params = (P0->c2 + P1->a2 + P2->v1)
}
one sig issue_proc_write_invalidc1a2v2 extends Act {} {
	params = (P0->c1 + P1->a2 + P2->v2)
}
one sig issue_proc_write_invalidc1a2v1 extends Act {} {
	params = (P0->c1 + P1->a2 + P2->v1)
}

one sig complete_proc_write_invalid extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Core + P1->Address + P2->Value
}
one sig complete_proc_write_invalidc2a1v2 extends Act {} {
	params = (P0->c2 + P1->a1 + P2->v2)
}
one sig complete_proc_write_invalidc1a1v2 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v2)
}
one sig complete_proc_write_invalidc2a1v1 extends Act {} {
	params = (P0->c2 + P1->a1 + P2->v1)
}
one sig complete_proc_write_invalidc1a1v1 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v1)
}
one sig complete_proc_write_invalidc1a2v2 extends Act {} {
	params = (P0->c1 + P1->a2 + P2->v2)
}
one sig complete_proc_write_invalidc1a2v1 extends Act {} {
	params = (P0->c1 + P1->a2 + P2->v1)
}

one sig do_bus_upgrade extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Core + P1->Address
}


one sig do_bus_read_for_ownership_invalid extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Core + P1->Address
}
one sig do_bus_read_for_ownership_invalidc1a1 extends Act {} {
	params = (P0->c1 + P1->a1)
}
one sig do_bus_read_for_ownership_invalidc2a2 extends Act {} {
	params = (P0->c2 + P1->a2)
}
one sig do_bus_read_for_ownership_invalidc2a1 extends Act {} {
	params = (P0->c2 + P1->a1)
}
one sig do_bus_read_for_ownership_invalidc1a2 extends Act {} {
	params = (P0->c1 + P1->a2)
}

one sig complete_proc_read_invalid_exclusive extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Core + P1->Address + P2->Value
}
one sig complete_proc_read_invalid_exclusivec1a1v1 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v1)
}
one sig complete_proc_read_invalid_exclusivec1a2v2 extends Act {} {
	params = (P0->c1 + P1->a2 + P2->v2)
}

one sig evict_modified extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Core + P1->Address
}
one sig evict_modifiedc1a1 extends Act {} {
	params = (P0->c1 + P1->a1)
}
one sig evict_modifiedc1a2 extends Act {} {
	params = (P0->c1 + P1->a2)
}

one sig complete_proc_read_invalid_shared extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Core + P1->Address + P2->Value
}


one sig issue_proc_write_shared extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Core + P1->Address + P2->Value
}
one sig issue_proc_write_sharedc2a1v2 extends Act {} {
	params = (P0->c2 + P1->a1 + P2->v2)
}
one sig issue_proc_write_sharedc1a1v2 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v2)
}
one sig issue_proc_write_sharedc2a1v1 extends Act {} {
	params = (P0->c2 + P1->a1 + P2->v1)
}
one sig issue_proc_write_sharedc1a1v1 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v1)
}
one sig issue_proc_write_sharedc1a2v2 extends Act {} {
	params = (P0->c1 + P1->a2 + P2->v2)
}
one sig issue_proc_write_sharedc1a2v1 extends Act {} {
	params = (P0->c1 + P1->a2 + P2->v1)
}

one sig issue_proc_read_invalid extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Core + P1->Address
}
one sig issue_proc_read_invalidc1a1 extends Act {} {
	params = (P0->c1 + P1->a1)
}
one sig issue_proc_read_invalidc2a2 extends Act {} {
	params = (P0->c2 + P1->a2)
}
one sig issue_proc_read_invalidc2a1 extends Act {} {
	params = (P0->c2 + P1->a1)
}
one sig issue_proc_read_invalidc1a2 extends Act {} {
	params = (P0->c1 + P1->a2)
}

one sig do_bus_read_for_ownership_valid extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Core + P1->Address + P2->Value
}
one sig do_bus_read_for_ownership_validc1a1v2 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v2)
}
one sig do_bus_read_for_ownership_validc1a1v1 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v1)
}

one sig proc_write_exclusive extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Core + P1->Address + P2->Value
}


one sig evict_exclusive_or_shared extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Core + P1->Address
}


one sig complete_proc_write_shared extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Core + P1->Address + P2->Value
}
one sig complete_proc_write_sharedc1a1v1 extends Act {} {
	params = (P0->c1 + P1->a1 + P2->v1)
}

one sig do_bus_read_invalid extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Core + P1->Address
}
one sig do_bus_read_invalidc1a1 extends Act {} {
	params = (P0->c1 + P1->a1)
}
one sig do_bus_read_invalidc2a2 extends Act {} {
	params = (P0->c2 + P1->a2)
}
one sig do_bus_read_invalidc2a1 extends Act {} {
	params = (P0->c2 + P1->a1)
}
one sig do_bus_read_invalidc1a2 extends Act {} {
	params = (P0->c1 + P1->a2)
}

one sig do_bus_read_valid extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Core + P1->Address + P2->Value
}



one sig T0, T1, T2, T3, T4, T5, T6, T7, T8 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6 + T6->T7 + T7->T8
	complete_proc_write_invalid in FlSymAction.baseName // the final base name in the neg trace must appear in the sep formula
}


fun envVarTypes : set(Var->Sort) {
	var2->Value + var1->Value + var0->Core
}


one sig var0, var1, var2 extends Var {} {}


one sig var0toc2var2tov1var1tov2 extends Env {} {}
one sig var0toc2var1tov1 extends Env {} {}
one sig var0toc1var1tov2 extends Env {} {}
one sig var0toc2var1tov1var2tov2 extends Env {} {}
one sig var0toc1var2tov2var1tov2 extends Env {} {}
one sig var0toc1 extends Env {} {}
one sig var0toc2var1tov2 extends Env {} {}
one sig var1tov1var0toc1var2tov1 extends Env {} {}
one sig var0toc2var1tov1var2tov1 extends Env {} {}
one sig var0toc1var2tov1var1tov2 extends Env {} {}
one sig var1tov1var0toc1var2tov2 extends Env {} {}
one sig var0toc2 extends Env {} {}
one sig var0toc2var2tov2var1tov2 extends Env {} {}
one sig var1tov1var0toc1 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT34->T4) + (PT1->T8) + (PT11->T4) + (PT13->T4) + (PT38->T5) + (PT28->T6) + (PT27->T7) + (PT39->T7) + (PT37->T5) + (PT8->T6) + (PT31->T4) + (PT36->T4) + (PT18->T4) + (PT21->T5) + (PT6->T3) + (PT12->T3) + (PT40->T7) + (PT20->T4) + (PT32->T5) + (PT33->T5) + (PT9->T4) + (PT14->T3) + (PT35->T6) + (PT10->T4) + (PT17->T4) + (PT19->T4) + (NT1->T8)

	path = (PT34 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->evict_modifiedc1a1 + T3->issue_proc_write_sharedc1a1v2 + T4->complete_proc_write_invalidc1a1v2)) +
		(PT1 -> (T0->issue_proc_write_invalidc1a1v1 + T1->do_bus_read_for_ownership_invalidc2a1 + T2->complete_proc_write_invalidc1a1v1 + T3->evict_modifiedc1a1 + T4->issue_proc_read_invalidc1a1 + T5->do_bus_read_invalidc2a1 + T6->complete_proc_read_invalid_exclusivec1a1v1 + T7->issue_proc_write_invalidc2a1v2 + T8->do_bus_read_for_ownership_validc1a1v2)) +
		(PT11 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->evict_modifiedc1a1 + T3->issue_proc_write_sharedc2a1v1 + T4->complete_proc_write_invalidc2a1v1)) +
		(PT13 -> (T0->issue_proc_write_invalidc1a1v1 + T1->complete_proc_write_sharedc1a1v1 + T2->issue_proc_write_invalidc1a1v2 + T3->do_bus_read_for_ownership_invalidc2a1 + T4->complete_proc_write_invalidc1a1v2)) +
		(PT38 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->issue_proc_read_invalidc1a2 + T3->do_bus_read_invalidc2a2 + T4->complete_proc_read_invalid_exclusivec1a2v2 + T5->issue_proc_write_invalidc2a1v2)) +
		(PT28 -> (T0->issue_proc_read_invalidc1a1 + T1->do_bus_read_invalidc2a1 + T2->complete_proc_read_invalid_exclusivec1a1v1 + T3->issue_proc_write_sharedc2a1v1 + T4->complete_proc_write_invalidc2a1v1 + T5->issue_proc_write_invalidc1a2v1 + T6->do_bus_read_for_ownership_invalidc2a2)) +
		(PT27 -> (T0->issue_proc_write_invalidc1a1v1 + T1->complete_proc_write_sharedc1a1v1 + T2->issue_proc_read_invalidc1a1 + T3->do_bus_read_invalidc2a1 + T4->do_bus_read_for_ownership_invalidc2a1 + T5->complete_proc_read_invalid_exclusivec1a1v1 + T6->issue_proc_write_sharedc2a1v1 + T7->complete_proc_write_invalidc2a1v1)) +
		(PT39 -> (T0->issue_proc_read_invalidc1a1 + T1->do_bus_read_invalidc2a1 + T2->complete_proc_read_invalid_exclusivec1a1v1 + T3->evict_modifiedc1a1 + T4->issue_proc_write_sharedc1a1v1 + T5->complete_proc_write_invalidc1a1v1 + T6->issue_proc_write_sharedc2a1v1 + T7->complete_proc_write_invalidc2a1v1)) +
		(PT37 -> (T0->issue_proc_read_invalidc1a1 + T1->do_bus_read_invalidc2a1 + T2->complete_proc_read_invalid_exclusivec1a1v1 + T3->issue_proc_write_sharedc1a2v2 + T4->complete_proc_write_invalidc1a2v2 + T5->issue_proc_write_invalidc2a1v1)) +
		(PT8 -> (T0->issue_proc_read_invalidc1a1 + T1->do_bus_read_invalidc2a1 + T2->complete_proc_read_invalid_exclusivec1a1v1 + T3->issue_proc_write_sharedc1a2v1 + T4->complete_proc_write_invalidc1a2v1 + T5->issue_proc_write_sharedc2a1v2 + T6->complete_proc_write_invalidc2a1v2)) +
		(PT31 -> (T0->issue_proc_write_invalidc1a1v1 + T1->do_bus_read_for_ownership_invalidc2a1 + T2->complete_proc_write_invalidc1a1v1 + T3->issue_proc_write_sharedc2a1v2 + T4->complete_proc_write_invalidc2a1v2)) +
		(PT36 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->evict_modifiedc1a1 + T3->issue_proc_read_invalidc2a1 + T4->do_bus_read_invalidc1a1)) +
		(PT18 -> (T0->issue_proc_write_invalidc1a1v1 + T1->do_bus_read_for_ownership_invalidc2a1 + T2->complete_proc_write_invalidc1a1v1 + T3->issue_proc_write_sharedc1a2v2 + T4->complete_proc_write_invalidc1a2v2)) +
		(PT21 -> (T0->issue_proc_write_invalidc1a1v1 + T1->do_bus_read_for_ownership_invalidc2a1 + T2->complete_proc_write_invalidc1a1v1 + T3->issue_proc_write_invalidc2a1v1 + T4->do_bus_read_for_ownership_validc1a1v1 + T5->complete_proc_write_invalidc2a1v1)) +
		(PT6 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->issue_proc_read_invalidc2a2 + T3->do_bus_read_invalidc1a2)) +
		(PT12 -> (T0->evict_modifiedc1a2 + T1->issue_proc_write_invalidc1a1v1 + T2->do_bus_read_for_ownership_invalidc2a1 + T3->complete_proc_write_invalidc1a1v1)) +
		(PT40 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->evict_modifiedc1a1 + T3->issue_proc_read_invalidc1a1 + T4->do_bus_read_invalidc2a1 + T5->complete_proc_read_invalid_exclusivec1a1v1 + T6->issue_proc_write_sharedc2a1v2 + T7->complete_proc_write_invalidc2a1v2)) +
		(PT20 -> (T0->issue_proc_write_invalidc1a1v1 + T1->do_bus_read_for_ownership_invalidc2a1 + T2->complete_proc_write_invalidc1a1v1 + T3->issue_proc_write_invalidc2a2v1 + T4->do_bus_read_for_ownership_invalidc1a2)) +
		(PT32 -> (T0->issue_proc_read_invalidc1a1 + T1->do_bus_read_invalidc2a1 + T2->complete_proc_read_invalid_exclusivec1a1v1 + T3->issue_proc_write_invalidc2a1v1 + T4->do_bus_read_for_ownership_validc1a1v1 + T5->complete_proc_write_invalidc2a1v1)) +
		(PT33 -> (T0->issue_proc_read_invalidc1a1 + T1->do_bus_read_invalidc2a1 + T2->complete_proc_read_invalid_exclusivec1a1v1 + T3->issue_proc_write_invalidc1a2v1 + T4->do_bus_read_for_ownership_invalidc2a2 + T5->complete_proc_write_invalidc1a2v1)) +
		(PT9 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->evict_modifiedc1a1 + T3->issue_proc_write_invalidc2a1v1 + T4->do_bus_read_for_ownership_invalidc1a1)) +
		(PT14 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->issue_proc_write_invalidc2a2v1 + T3->do_bus_read_for_ownership_invalidc1a2)) +
		(PT35 -> (T0->issue_proc_read_invalidc1a1 + T1->do_bus_read_invalidc2a1 + T2->complete_proc_read_invalid_exclusivec1a1v1 + T3->issue_proc_write_sharedc1a2v1 + T4->complete_proc_write_invalidc1a2v1 + T5->issue_proc_write_sharedc2a1v1 + T6->complete_proc_write_invalidc2a1v1)) +
		(PT10 -> (T0->issue_proc_write_invalidc1a1v1 + T1->do_bus_read_for_ownership_invalidc2a1 + T2->complete_proc_write_invalidc1a1v1 + T3->issue_proc_write_sharedc2a1v1 + T4->complete_proc_write_invalidc2a1v1)) +
		(PT17 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->issue_proc_write_sharedc2a1v1 + T3->complete_proc_write_invalidc2a1v1 + T4->issue_proc_read_invalidc1a2)) +
		(PT19 -> (T0->issue_proc_write_sharedc1a1v1 + T1->complete_proc_write_invalidc1a1v1 + T2->issue_proc_write_invalidc1a2v2 + T3->do_bus_read_for_ownership_invalidc2a2 + T4->complete_proc_write_invalidc1a2v2)) +
		(NT1 -> (T0->issue_proc_write_invalidc1a1v1 + T1->do_bus_read_for_ownership_invalidc2a1 + T2->complete_proc_write_invalidc1a1v1 + T3->evict_modifiedc1a1 + T4->issue_proc_read_invalidc1a1 + T5->do_bus_read_invalidc2a1 + T6->complete_proc_read_invalid_exclusivec1a1v1 + T7->issue_proc_write_invalidc2a1v2 + T8->complete_proc_write_invalidc2a1v2))

	maps = var0toc2var2tov1var1tov2->(var0->c2 + var2->v1 + var1->v2) +
		var0toc2var1tov1->(var0->c2 + var1->v1) +
		var0toc1var1tov2->(var0->c1 + var1->v2) +
		var0toc2var1tov1var2tov2->(var0->c2 + var1->v1 + var2->v2) +
		var0toc1var2tov2var1tov2->(var0->c1 + var2->v2 + var1->v2) +
		var0toc1->(var0->c1) +
		var0toc2var1tov2->(var0->c2 + var1->v2) +
		var1tov1var0toc1var2tov1->(var1->v1 + var0->c1 + var2->v1) +
		var0toc2var1tov1var2tov1->(var0->c2 + var1->v1 + var2->v1) +
		var0toc1var2tov1var1tov2->(var0->c1 + var2->v1 + var1->v2) +
		var1tov1var0toc1var2tov2->(var1->v1 + var0->c1 + var2->v2) +
		var0toc2->(var0->c2) +
		var0toc2var2tov2var1tov2->(var0->c2 + var2->v2 + var1->v2) +
		var1tov1var0toc1->(var1->v1 + var0->c1)

	baseName = issue_proc_write_invalidc2a1v1->issue_proc_write_invalid +
		issue_proc_write_invalidc2a1v2->issue_proc_write_invalid +
		issue_proc_write_invalidc2a2v1->issue_proc_write_invalid +
		complete_proc_write_sharedc1a1v1->complete_proc_write_shared +
		issue_proc_write_invalidc1a1v1->issue_proc_write_invalid +
		issue_proc_write_invalidc1a1v2->issue_proc_write_invalid +
		issue_proc_write_invalidc1a2v1->issue_proc_write_invalid +
		issue_proc_write_invalidc1a2v2->issue_proc_write_invalid +
		complete_proc_read_invalid_exclusivec1a1v1->complete_proc_read_invalid_exclusive +
		complete_proc_read_invalid_exclusivec1a2v2->complete_proc_read_invalid_exclusive +
		issue_proc_write_sharedc1a1v2->issue_proc_write_shared +
		issue_proc_write_sharedc1a2v2->issue_proc_write_shared +
		issue_proc_write_sharedc1a2v1->issue_proc_write_shared +
		issue_proc_write_sharedc1a1v1->issue_proc_write_shared +
		do_bus_read_invalidc1a1->do_bus_read_invalid +
		complete_proc_write_invalidc2a1v2->complete_proc_write_invalid +
		complete_proc_write_invalidc2a1v1->complete_proc_write_invalid +
		do_bus_read_invalidc2a2->do_bus_read_invalid +
		do_bus_read_invalidc2a1->do_bus_read_invalid +
		do_bus_read_invalidc1a2->do_bus_read_invalid +
		issue_proc_read_invalidc1a1->issue_proc_read_invalid +
		issue_proc_write_sharedc2a1v2->issue_proc_write_shared +
		issue_proc_write_sharedc2a1v1->issue_proc_write_shared +
		complete_proc_write_invalidc1a1v1->complete_proc_write_invalid +
		do_bus_read_for_ownership_validc1a1v1->do_bus_read_for_ownership_valid +
		do_bus_read_for_ownership_invalidc1a1->do_bus_read_for_ownership_invalid +
		complete_proc_write_invalidc1a2v2->complete_proc_write_invalid +
		do_bus_read_for_ownership_invalidc2a1->do_bus_read_for_ownership_invalid +
		do_bus_read_for_ownership_invalidc1a2->do_bus_read_for_ownership_invalid +
		complete_proc_write_invalidc1a1v2->complete_proc_write_invalid +
		complete_proc_write_invalidc1a2v1->complete_proc_write_invalid +
		do_bus_read_for_ownership_invalidc2a2->do_bus_read_for_ownership_invalid +
		do_bus_read_for_ownership_validc1a1v2->do_bus_read_for_ownership_valid +
		evict_modifiedc1a1->evict_modified +
		evict_modifiedc1a2->evict_modified +
		issue_proc_read_invalidc2a2->issue_proc_read_invalid +
		issue_proc_read_invalidc2a1->issue_proc_read_invalid +
		issue_proc_read_invalidc1a2->issue_proc_read_invalid
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT34 extends PosTrace {} {}
one sig PT1 extends PosTrace {} {}
one sig PT11 extends PosTrace {} {}
one sig PT13 extends PosTrace {} {}
one sig PT38 extends PosTrace {} {}
one sig PT28 extends PosTrace {} {}
one sig PT27 extends PosTrace {} {}
one sig PT39 extends PosTrace {} {}
one sig PT37 extends PosTrace {} {}
one sig PT8 extends PosTrace {} {}
one sig PT31 extends PosTrace {} {}
one sig PT36 extends PosTrace {} {}
one sig PT18 extends PosTrace {} {}
one sig PT21 extends PosTrace {} {}
one sig PT6 extends PosTrace {} {}
one sig PT12 extends PosTrace {} {}
one sig PT40 extends PosTrace {} {}
one sig PT20 extends PosTrace {} {}
one sig PT32 extends PosTrace {} {}
one sig PT33 extends PosTrace {} {}
one sig PT9 extends PosTrace {} {}
one sig PT14 extends PosTrace {} {}
one sig PT35 extends PosTrace {} {}
one sig PT10 extends PosTrace {} {}
one sig PT17 extends PosTrace {} {}
one sig PT19 extends PosTrace {} {}
