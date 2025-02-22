//36
open util/boolean
open util/ordering[Idx] as IdxOrder
open util/ordering[ParamIdx] as ParamIdxOrder

abstract sig Var {}

abstract sig Atom {}

abstract sig Sort {
	atoms : some Atom,
	setSort : Bool,
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
	child in (Fluent + VarEquals + VarSetMutex + VarLTE)
}

sig Implies extends Formula {
	left : Formula,
	right : Formula
} {
	children = left + right
}

sig FlSymAction {
    baseName : BaseName,

    // actToFlParamsMap maps action-params to fluent-params
    // in other words, actToFlParamsMap decides which of the action-params will be
    // used for setting a boolean value of the state variable (representing the
    // fluent) in the _hist TLA+ code.
    actToFlParamsMap : set(ParamIdx->ParamIdx)
} {
    // domain(actToFlParamsMap) \subseteq paramIdxs(baseName)
    actToFlParamsMap.ParamIdx in baseName.paramIdxs

    // actToFlParamsMap is a function
    all k,v1,v2 : ParamIdx | (k->v1 in actToFlParamsMap and k->v2 in actToFlParamsMap) implies (v1 = v2)
    // actToFlParamsMap is injective
    all k1,k2,v : ParamIdx | (k1->v in actToFlParamsMap and k2->v in actToFlParamsMap) implies (k1 = k2)
}

sig Fluent extends Formula {
    initially : Bool,
    initFl : set FlSymAction,
    termFl : set FlSymAction,
    mutInitFl : set FlSymAction,
    falsifyFl : set FlSymAction,

    // vars represents the parameters (including the ordering) to the fluent itself
    vars : set(ParamIdx->Var)
} {
    no children
    some vars

    // no fancy fluents for now
    no mutInitFl
    no falsifyFl

    // strong condition for ensuring each fluent category is mutex
    no initFl.baseName & termFl.baseName
    no initFl.baseName & mutInitFl.baseName
    no initFl.baseName & falsifyFl.baseName
    no termFl.baseName & mutInitFl.baseName
    no termFl.baseName & falsifyFl.baseName
    no mutInitFl.baseName & falsifyFl.baseName
    some initFl + termFl + mutInitFl + falsifyFl

    // vars is a function
    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)

    // each fluent must accept all the fluent params in vars
    all s : (initFl+termFl+mutInitFl+falsifyFl) | ParamIdx.(s.actToFlParamsMap) = vars.Var

    // each action must input the same param-types to the fluent
    let flParamTypes = vars.envVarTypes |
        all a : (initFl+termFl+mutInitFl+falsifyFl) |
            // for each param in the action, its type must match the fluent
            all actIdx : a.actToFlParamsMap.ParamIdx |
                let flIdx = actIdx.(a.actToFlParamsMap) |
                    flIdx.flParamTypes = actIdx.(a.baseName.paramTypes)

    // actToFlParamsMap is an injective function
    // furthermore, when we combine actToFlParamsMap across all actions, the combination
    // must STILL be injective
    all x1,x2,y1,y2 : ParamIdx |
    let allFluents = initFl+termFl+mutInitFl+falsifyFl |
        (x1->y1 in allFluents.actToFlParamsMap and x2->y2 in allFluents.actToFlParamsMap) implies (x1->y1 = x2->y2 or (not x1=x2 and not y1=y2))

    no falsifyFl.actToFlParamsMap // falsify fluents don't take params

    initially = False // speed optimization, also makes the fluent easier to read
}

sig VarEquals extends Formula {
    lhs : Var,
    rhs : Var
} {
	no children
	lhs != rhs
	lhs.envVarTypes = rhs.envVarTypes // only compare vars of the same type
}

sig VarSetMutex extends Formula {
    sort : Sort,
    lhs : Var,
    rhs : Var
} {
	no children
	lhs != rhs
	lhs.envVarTypes = sort
	rhs.envVarTypes = sort
	sort.setSort = True // the sort type must contain sets
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
	all f : Formula | f in Root.*children // not strictly needed, but seems to make things faster

	// no free vars, all vars must be used in the matrix
	let varsInMatrix = ParamIdx.(Fluent.vars) + VarEquals.lhs + VarEquals.rhs |
		varsInMatrix = (Forall.var + Exists.var)

	// do not quantify over a variable that's already in scope
	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)

	// speed optimization: require lhs to not have have an Implies node
	// we declare this here (instead of in Implies) because referring to 'children'
	// results in an error (due to weird scoping).
	all f : Implies | f.left.*children not in Implies

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
	satisfies : Env -> Idx -> Formula // formulas that satisfy this trace
} {
	// trace semantics, i.e. e |- t,i |= f, where e is an environment, t is a trace, i is an index, and f is a formula
	all e : Env, i : Idx, f : Not | e->i->f in satisfies iff (e->i->f.child not in satisfies)
	all e : Env, i : Idx, f : Implies | e->i->f in satisfies iff (e->i->f.left in satisfies implies e->i->f.right in satisfies)
	all e : Env, i : Idx, f : VarEquals | e->i->f in satisfies iff (f.lhs).(e.maps) = (f.rhs).(e.maps)
	all e : Env, i : Idx, f : VarSetMutex | e->i->f in satisfies iff
        (all s : f.sort.atoms | not setContains[s,(f.lhs).(e.maps)] or not setContains[s,(f.rhs).(e.maps)])
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
    some s : (f.initFl+f.mutInitFl) |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps
}

// does this action terminate the fluent?
pred isTermAct[a : Act, e : Env, f : Fluent] {
    (some s : f.termFl |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps)
    or
    (some s : f.mutInitFl |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) not in e.maps)
    or
    (some s : f.falsifyFl |
        a.baseName = s.baseName)
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


/* main */
run {
	// find a formula that separates "good" traces from "bad" ones
	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies
	all nt : NegTrace | no (EmptyEnv->nt.lastIdx->Root & nt.satisfies)
	EmptyEnv->T0->Root in EmptyTrace.satisfies // the formula must satisfy the empty trace
	minsome children // smallest formula possible
	minsome FlSymAction // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent // fewer fluents makes local inductive invariant inference easier
}
for 8 Formula, 5 FlSymAction

one sig P0 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = none->none
	all f : Fluent | (f.vars.Var = P0)
}



pred setContains[s : Atom, e : Atom] {
	let containsRel = (none->none) |
		(s->e) in containsRel
}


pred lte[lhs : Atom, rhs : Atom] {
	let containsRel = (none->none) |
		(lhs->rhs) in containsRel
}


one sig r2, r3, r1 extends Atom {}

one sig RMs extends Sort {} {
	atoms = r2 + r3 + r1
	setSort = False
	numericSort = False
}

one sig SndAbort extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig SndAbortr1 extends Act {} {
	params = (P0->r1)
}
one sig SndAbortr2 extends Act {} {
	params = (P0->r2)
}

one sig RcvPrepare extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig RcvPreparer3 extends Act {} {
	params = (P0->r3)
}
one sig RcvPreparer1 extends Act {} {
	params = (P0->r1)
}
one sig RcvPreparer2 extends Act {} {
	params = (P0->r2)
}

one sig SndCommit extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig SndCommitr1 extends Act {} {
	params = (P0->r1)
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

one sig SilentAbort extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig SilentAbortr1 extends Act {} {
	params = (P0->r1)
}

one sig RcvAbort extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig RcvAbortr3 extends Act {} {
	params = (P0->r3)
}
one sig RcvAbortr1 extends Act {} {
	params = (P0->r1)
}
one sig RcvAbortr2 extends Act {} {
	params = (P0->r2)
}

one sig RcvCommit extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig RcvCommitr1 extends Act {} {
	params = (P0->r1)
}
one sig RcvCommitr2 extends Act {} {
	params = (P0->r2)
}


one sig T0, T1, T2, T3, T4, T5, T6, T7, T8, T9 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6 + T6->T7 + T7->T8 + T8->T9

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
	lastIdx = (EmptyTrace->T0) + (PT8->T4) + (PT9->T4) + (PT10->T7) + (PT11->T7) + (PT12->T0) + (PT13->T7) + (NT1->T9)

	path = (PT8 -> (T0->SndPreparer1 + T1->SndAbortr1 + T2->RcvAbortr1 + T3->SndPreparer2 + T4->SndPreparer3)) +
		(PT9 -> (T0->SndAbortr1 + T1->SndPreparer1 + T2->RcvAbortr1 + T3->RcvAbortr2 + T4->RcvAbortr3)) +
		(PT10 -> (T0->SndPreparer1 + T1->RcvPreparer1 + T2->SndPreparer2 + T3->RcvPreparer2 + T4->SndPreparer3 + T5->RcvPreparer3 + T6->SndAbortr1 + T7->RcvAbortr1)) +
		(PT11 -> (T0->SndPreparer1 + T1->SndPreparer2 + T2->RcvPreparer1 + T3->RcvPreparer2 + T4->SndPreparer3 + T5->RcvPreparer3 + T6->SndCommitr1 + T7->RcvCommitr1)) +
		(PT12 -> (T0->SilentAbortr1)) +
		(PT13 -> (T0->SndPreparer1 + T1->SndPreparer2 + T2->RcvPreparer1 + T3->SndPreparer3 + T4->RcvPreparer2 + T5->RcvPreparer3 + T6->SndCommitr1 + T7->RcvCommitr2)) +
		(NT1 -> (T0->SndPreparer1 + T1->RcvPreparer1 + T2->SndCommitr1 + T3->SndPreparer2 + T4->RcvPreparer2 + T5->SndAbortr2 + T6->RcvAbortr3 + T7->SndPreparer3 + T8->RcvPreparer3 + T9->RcvCommitr1))

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

	baseName = RcvAbortr2->RcvAbort +
		RcvAbortr1->RcvAbort +
		SilentAbortr1->SilentAbort +
		RcvAbortr3->RcvAbort +
		SndAbortr1->SndAbort +
		SndPreparer2->SndPrepare +
		SndAbortr2->SndAbort +
		SndPreparer3->SndPrepare +
		SndPreparer1->SndPrepare +
		RcvPreparer3->RcvPrepare +
		RcvPreparer2->RcvPrepare +
		RcvPreparer1->RcvPrepare +
		SndCommitr1->SndCommit +
		RcvCommitr2->RcvCommit +
		RcvCommitr1->RcvCommit
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT8 extends PosTrace {} {}
one sig PT9 extends PosTrace {} {}
one sig PT10 extends PosTrace {} {}
one sig PT11 extends PosTrace {} {}
one sig PT12 extends PosTrace {} {}
one sig PT13 extends PosTrace {} {}
