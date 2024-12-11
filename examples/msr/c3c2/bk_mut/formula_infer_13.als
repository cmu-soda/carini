//7
open util/boolean
open util/ordering[Idx] as IdxOrder
open util/ordering[ParamIdx] as ParamIdxOrder

abstract sig Var {}

abstract sig Atom {}

abstract sig Sort {
	atoms : some Atom
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
	child in (Fluent + VarEquals)
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

    // fix the order of the param map to be ascending (since the order doesn't matter).
    // the idea is to make the ordering deterministic and, hopefully, result in a faster run time.
    all a1,f1,a2,f2 : ParamIdx |
        (a1->f1 in actToFlParamsMap and a2->f2 in actToFlParamsMap and a1.lt[a2]) implies (f1.lt[f2])
}

sig Fluent extends Formula {
    initially : Bool,
    initFl : set FlSymAction,
    termFl : set FlSymAction,
    mutInitFl : set FlSymAction,
    mutTermFl : set FlSymAction,

    // vars represents the parameters (including the ordering) to the fluent itself
    vars : set(ParamIdx->Var)
} {
    no children
    some vars

    // strong condition for ensuring each fluent category is mutex
    no initFl.baseName & termFl.baseName
    no initFl.baseName & mutInitFl.baseName
    no initFl.baseName & mutTermFl.baseName
    no termFl.baseName & mutInitFl.baseName
    no termFl.baseName & mutTermFl.baseName
    no mutInitFl.baseName & mutTermFl.baseName
    some initFl + termFl + mutInitFl + mutTermFl

    // vars is a function
    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)

    // each fluent must accept all the fluent params in vars
    all s : (initFl+termFl+mutInitFl+mutTermFl) | ParamIdx.(s.actToFlParamsMap) = vars.Var

    // each action must input the same param-types to the fluent
    let flParamTypes = vars.envVarTypes |
        all a : (initFl+termFl+mutInitFl+mutTermFl) |
            // for each param in the action, its type must match the fluent
            all actIdx : a.actToFlParamsMap.ParamIdx |
                let flIdx = actIdx.(a.actToFlParamsMap) |
                    flIdx.flParamTypes = actIdx.(a.baseName.paramTypes)

    // actToFlParamsMap is an injective function
    // furthermore, when we combine actToFlParamsMap across all actions, the combination
    // must STILL be injective
    all x1,x2,y1,y2 : ParamIdx |
    let allFluents = initFl+termFl+mutInitFl+mutTermFl |
        (x1->y1 in allFluents.actToFlParamsMap and x2->y2 in allFluents.actToFlParamsMap) implies (x1->y1 = x2->y2 or (not x1=x2 and not y1=y2))

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
    (some s : (f.initFl+f.mutInitFl) |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps)
    or
    (some s : f.mutTermFl |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) not in e.maps)
}

// does this action terminate the fluent?
pred isTermAct[a : Act, e : Env, f : Fluent] {
    (some s : (f.termFl+f.mutTermFl) |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps)
    or
    (some s : f.mutInitFl |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) not in e.maps)
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
	minsome initFl + termFl + mutInitFl + mutTermFl // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent // fewer fluents makes local inductive invariant inference easier
}
for 9 Formula, 5 FlSymAction

one sig P0, P1, P2, P3 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = P0->P1 + P1->P2 + P2->P3
	all f : Fluent | (f.vars.Var = P0) or (f.vars.Var = P0+P1) or (f.vars.Var = P0+P1+P2) or (f.vars.Var = P0+P1+P2+P3)
}



one sig n1, n2, n3, _n2n3_, _n1n2n3_, NUM2, NUM3, _n1n3_, _n1n2_, NUM0, NUM1 extends Atom {}

one sig Server extends Sort {} {
	atoms = n1 + n2 + n3
}
one sig Quorums extends Sort {} {
	atoms = _n2n3_ + _n1n2n3_ + _n1n3_ + _n1n2_
}
one sig FinNat extends Sort {} {
	atoms = NUM2 + NUM3 + NUM0 + NUM1
}

one sig RollbackEntries extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Server + P1->Server
}


one sig GetEntries extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Server + P1->Server
}


one sig BecomeLeader extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Server + P1->Quorums + P2->FinNat
}
one sig BecomeLeadern2_n2n3_NUM0 extends Act {} {
	params = (P0->n2 + P1->_n2n3_ + P2->NUM0)
}
one sig BecomeLeadern2_n2n3_NUM2 extends Act {} {
	params = (P0->n2 + P1->_n2n3_ + P2->NUM2)
}
one sig BecomeLeadern2_n1n2_NUM2 extends Act {} {
	params = (P0->n2 + P1->_n1n2_ + P2->NUM2)
}
one sig BecomeLeadern1_n1n2_NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM1)
}
one sig BecomeLeadern1_n1n2_NUM2 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM2)
}

one sig CommitEntry extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3
	paramTypes = P0->Server + P1->Quorums + P2->FinNat + P3->FinNat
}
one sig CommitEntryn1_n1n2_NUM1NUM2 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM1 + P3->NUM2)
}
one sig CommitEntryn1_n1n2_NUM1NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM1 + P3->NUM1)
}
one sig CommitEntryn2_n1n2_NUM1NUM2 extends Act {} {
	params = (P0->n2 + P1->_n1n2_ + P2->NUM1 + P3->NUM2)
}
one sig CommitEntryn1_n1n3_NUM1NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n3_ + P2->NUM1 + P3->NUM1)
}
one sig CommitEntryn2_n1n2_NUM1NUM0 extends Act {} {
	params = (P0->n2 + P1->_n1n2_ + P2->NUM1 + P3->NUM0)
}
one sig CommitEntryn1_n1n3_NUM2NUM2 extends Act {} {
	params = (P0->n1 + P1->_n1n3_ + P2->NUM2 + P3->NUM2)
}
one sig CommitEntryn1_n1n3_NUM2NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n3_ + P2->NUM2 + P3->NUM1)
}
one sig CommitEntryn2_n1n3_NUM1NUM2 extends Act {} {
	params = (P0->n2 + P1->_n1n3_ + P2->NUM1 + P3->NUM2)
}

one sig ClientRequest extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Server + P1->FinNat
}
one sig ClientRequestn2NUM0 extends Act {} {
	params = (P0->n2 + P1->NUM0)
}
one sig ClientRequestn1NUM1 extends Act {} {
	params = (P0->n1 + P1->NUM1)
}
one sig ClientRequestn2NUM2 extends Act {} {
	params = (P0->n2 + P1->NUM2)
}


one sig T0, T1, T2, T3, T4, T5 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5

}


fun envVarTypes : set(Var->Sort) {
	var2->Server + var1->Quorums + var0->Quorums
}


one sig var2, var1, var0 extends Var {} {}


one sig var2ton3var0to_n1n2n3_var1to_n2n3_ extends Env {} {}
one sig var2ton3var1to_n1n2n3_var0to_n2n3_ extends Env {} {}
one sig var2ton3var0to_n1n2_var1to_n2n3_ extends Env {} {}
one sig var2ton3var1to_n1n2_var0to_n2n3_ extends Env {} {}
one sig var0to_n1n3_ extends Env {} {}
one sig var1to_n1n3_var0to_n1n2_var2ton1 extends Env {} {}
one sig var0to_n1n3_var1to_n1n2_var2ton1 extends Env {} {}
one sig var1to_n1n3_var0to_n1n3_ extends Env {} {}
one sig var0to_n1n3_var1to_n1n2n3_var2ton1 extends Env {} {}
one sig var1to_n1n3_var0to_n1n2n3_var2ton1 extends Env {} {}
one sig var0to_n1n2n3_var2ton1var1to_n2n3_ extends Env {} {}
one sig var1to_n1n2n3_var2ton1var0to_n2n3_ extends Env {} {}
one sig var2ton3var1to_n1n3_var0to_n1n2_ extends Env {} {}
one sig var2ton3var0to_n1n3_var1to_n1n2_ extends Env {} {}
one sig var2ton2var0to_n2n3_var1to_n2n3_ extends Env {} {}
one sig var0to_n1n3_var2ton2var1to_n2n3_ extends Env {} {}
one sig var1to_n1n3_var2ton2var0to_n2n3_ extends Env {} {}
one sig var2ton3var0to_n1n3_var1to_n1n2n3_ extends Env {} {}
one sig var2ton3var1to_n1n3_var0to_n1n2n3_ extends Env {} {}
one sig var0to_n1n3_var1to_n1n2n3_ extends Env {} {}
one sig var1to_n1n3_var0to_n1n2n3_ extends Env {} {}
one sig var0to_n1n2_var1to_n1n2_var2ton2 extends Env {} {}
one sig var1to_n1n2n3_var0to_n1n2n3_var2ton2 extends Env {} {}
one sig var1to_n1n3_var0to_n1n2_ extends Env {} {}
one sig var0to_n1n3_var1to_n1n2_ extends Env {} {}
one sig var2ton3var1to_n1n3_var0to_n1n3_ extends Env {} {}
one sig var0to_n1n2_var1to_n1n2n3_var2ton2 extends Env {} {}
one sig var1to_n1n2_var0to_n1n2n3_var2ton2 extends Env {} {}
one sig var0to_n1n3_var1to_n2n3_ extends Env {} {}
one sig var1to_n1n3_var0to_n2n3_ extends Env {} {}
one sig var0to_n1n3_var1to_n1n2n3_var2ton2 extends Env {} {}
one sig var1to_n1n3_var0to_n1n2n3_var2ton2 extends Env {} {}
one sig var1to_n1n3_var0to_n1n2_var2ton2 extends Env {} {}
one sig var0to_n1n3_var1to_n1n2_var2ton2 extends Env {} {}
one sig var0to_n1n2_var2ton2var1to_n2n3_ extends Env {} {}
one sig var1to_n1n2_var2ton2var0to_n2n3_ extends Env {} {}
one sig var0to_n1n2n3_var2ton2var1to_n2n3_ extends Env {} {}
one sig var1to_n1n2n3_var2ton2var0to_n2n3_ extends Env {} {}
one sig var0to_n1n2_var1to_n1n2_ extends Env {} {}
one sig var0to_n1n3_var2ton1var1to_n2n3_ extends Env {} {}
one sig var1to_n1n3_var2ton1var0to_n2n3_ extends Env {} {}
one sig var0to_n1n2_var1to_n1n2n3_ extends Env {} {}
one sig var1to_n1n2_var0to_n1n2n3_ extends Env {} {}
one sig var1to_n1n3_var0to_n1n3_var2ton1 extends Env {} {}
one sig var1to_n1n2n3_var0to_n1n2n3_ extends Env {} {}
one sig var2ton3var0to_n2n3_var1to_n2n3_ extends Env {} {}
one sig var2ton1var0to_n2n3_var1to_n2n3_ extends Env {} {}
one sig var0to_n1n2_var1to_n2n3_ extends Env {} {}
one sig var1to_n1n2_var0to_n2n3_ extends Env {} {}
one sig var0to_n1n2_var1to_n1n2_var2ton1 extends Env {} {}
one sig var0to_n1n2n3_var1to_n2n3_ extends Env {} {}
one sig var1to_n1n2n3_var0to_n2n3_ extends Env {} {}
one sig var0to_n1n2_var1to_n1n2n3_var2ton1 extends Env {} {}
one sig var1to_n1n2_var0to_n1n2n3_var2ton1 extends Env {} {}
one sig var1to_n1n2n3_var0to_n1n2n3_var2ton1 extends Env {} {}
one sig var0to_n1n2_ extends Env {} {}
one sig var0to_n1n2n3_ extends Env {} {}
one sig var1to_n1n3_var0to_n1n3_var2ton2 extends Env {} {}
one sig var2ton3var0to_n1n3_var1to_n2n3_ extends Env {} {}
one sig var2ton3var1to_n1n3_var0to_n2n3_ extends Env {} {}
one sig var2ton3var1to_n1n2n3_var0to_n1n2n3_ extends Env {} {}
one sig var2ton3var0to_n1n2_var1to_n1n2n3_ extends Env {} {}
one sig var2ton3var1to_n1n2_var0to_n1n2n3_ extends Env {} {}
one sig var2ton3var0to_n1n2_var1to_n1n2_ extends Env {} {}
one sig var0to_n1n2_var2ton1var1to_n2n3_ extends Env {} {}
one sig var1to_n1n2_var2ton1var0to_n2n3_ extends Env {} {}
one sig var0to_n2n3_var1to_n2n3_ extends Env {} {}
one sig var0to_n2n3_ extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT25->T3) + (PT30->T4) + (PT27->T4) + (NT1->T5) + (PT32->T4) + (PT26->T4) + (PT28->T4) + (PT24->T3) + (PT31->T3) + (PT29->T2)

	path = (PT25 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->CommitEntryn1_n1n2_NUM1NUM1)) +
		(PT30 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern1_n1n2_NUM2 + T3->CommitEntryn1_n1n3_NUM2NUM2 + T4->CommitEntryn1_n1n2_NUM1NUM2)) +
		(PT27 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->CommitEntryn2_n1n3_NUM1NUM2 + T4->CommitEntryn1_n1n2_NUM1NUM1)) +
		(NT1 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM0 + T3->ClientRequestn2NUM0 + T4->CommitEntryn1_n1n3_NUM1NUM1 + T5->CommitEntryn2_n1n2_NUM1NUM0)) +
		(PT32 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n1n2_NUM2 + T3->ClientRequestn2NUM2 + T4->CommitEntryn2_n1n2_NUM1NUM2)) +
		(PT26 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->CommitEntryn1_n1n2_NUM1NUM1)) +
		(PT28 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->CommitEntryn1_n1n3_NUM2NUM1 + T4->CommitEntryn2_n1n2_NUM1NUM2)) +
		(PT24 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->CommitEntryn1_n1n2_NUM1NUM1 + T3->CommitEntryn1_n1n3_NUM1NUM1)) +
		(PT31 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->BecomeLeadern2_n2n3_NUM2 + T2->CommitEntryn1_n1n3_NUM1NUM1 + T3->CommitEntryn2_n1n2_NUM1NUM2)) +
		(PT29 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->CommitEntryn1_n1n3_NUM1NUM1))

	maps = var2ton3var0to_n1n2n3_var1to_n2n3_->(var2->n3 + var0->_n1n2n3_ + var1->_n2n3_) +
		var2ton3var1to_n1n2n3_var0to_n2n3_->(var2->n3 + var1->_n1n2n3_ + var0->_n2n3_) +
		var2ton3var0to_n1n2_var1to_n2n3_->(var2->n3 + var0->_n1n2_ + var1->_n2n3_) +
		var2ton3var1to_n1n2_var0to_n2n3_->(var2->n3 + var1->_n1n2_ + var0->_n2n3_) +
		var0to_n1n3_->(var0->_n1n3_) +
		var1to_n1n3_var0to_n1n2_var2ton1->(var1->_n1n3_ + var0->_n1n2_ + var2->n1) +
		var0to_n1n3_var1to_n1n2_var2ton1->(var0->_n1n3_ + var1->_n1n2_ + var2->n1) +
		var1to_n1n3_var0to_n1n3_->(var1->_n1n3_ + var0->_n1n3_) +
		var0to_n1n3_var1to_n1n2n3_var2ton1->(var0->_n1n3_ + var1->_n1n2n3_ + var2->n1) +
		var1to_n1n3_var0to_n1n2n3_var2ton1->(var1->_n1n3_ + var0->_n1n2n3_ + var2->n1) +
		var0to_n1n2n3_var2ton1var1to_n2n3_->(var0->_n1n2n3_ + var2->n1 + var1->_n2n3_) +
		var1to_n1n2n3_var2ton1var0to_n2n3_->(var1->_n1n2n3_ + var2->n1 + var0->_n2n3_) +
		var2ton3var1to_n1n3_var0to_n1n2_->(var2->n3 + var1->_n1n3_ + var0->_n1n2_) +
		var2ton3var0to_n1n3_var1to_n1n2_->(var2->n3 + var0->_n1n3_ + var1->_n1n2_) +
		var2ton2var0to_n2n3_var1to_n2n3_->(var2->n2 + var0->_n2n3_ + var1->_n2n3_) +
		var0to_n1n3_var2ton2var1to_n2n3_->(var0->_n1n3_ + var2->n2 + var1->_n2n3_) +
		var1to_n1n3_var2ton2var0to_n2n3_->(var1->_n1n3_ + var2->n2 + var0->_n2n3_) +
		var2ton3var0to_n1n3_var1to_n1n2n3_->(var2->n3 + var0->_n1n3_ + var1->_n1n2n3_) +
		var2ton3var1to_n1n3_var0to_n1n2n3_->(var2->n3 + var1->_n1n3_ + var0->_n1n2n3_) +
		var0to_n1n3_var1to_n1n2n3_->(var0->_n1n3_ + var1->_n1n2n3_) +
		var1to_n1n3_var0to_n1n2n3_->(var1->_n1n3_ + var0->_n1n2n3_) +
		var0to_n1n2_var1to_n1n2_var2ton2->(var0->_n1n2_ + var1->_n1n2_ + var2->n2) +
		var1to_n1n2n3_var0to_n1n2n3_var2ton2->(var1->_n1n2n3_ + var0->_n1n2n3_ + var2->n2) +
		var1to_n1n3_var0to_n1n2_->(var1->_n1n3_ + var0->_n1n2_) +
		var0to_n1n3_var1to_n1n2_->(var0->_n1n3_ + var1->_n1n2_) +
		var2ton3var1to_n1n3_var0to_n1n3_->(var2->n3 + var1->_n1n3_ + var0->_n1n3_) +
		var0to_n1n2_var1to_n1n2n3_var2ton2->(var0->_n1n2_ + var1->_n1n2n3_ + var2->n2) +
		var1to_n1n2_var0to_n1n2n3_var2ton2->(var1->_n1n2_ + var0->_n1n2n3_ + var2->n2) +
		var0to_n1n3_var1to_n2n3_->(var0->_n1n3_ + var1->_n2n3_) +
		var1to_n1n3_var0to_n2n3_->(var1->_n1n3_ + var0->_n2n3_) +
		var0to_n1n3_var1to_n1n2n3_var2ton2->(var0->_n1n3_ + var1->_n1n2n3_ + var2->n2) +
		var1to_n1n3_var0to_n1n2n3_var2ton2->(var1->_n1n3_ + var0->_n1n2n3_ + var2->n2) +
		var1to_n1n3_var0to_n1n2_var2ton2->(var1->_n1n3_ + var0->_n1n2_ + var2->n2) +
		var0to_n1n3_var1to_n1n2_var2ton2->(var0->_n1n3_ + var1->_n1n2_ + var2->n2) +
		var0to_n1n2_var2ton2var1to_n2n3_->(var0->_n1n2_ + var2->n2 + var1->_n2n3_) +
		var1to_n1n2_var2ton2var0to_n2n3_->(var1->_n1n2_ + var2->n2 + var0->_n2n3_) +
		var0to_n1n2n3_var2ton2var1to_n2n3_->(var0->_n1n2n3_ + var2->n2 + var1->_n2n3_) +
		var1to_n1n2n3_var2ton2var0to_n2n3_->(var1->_n1n2n3_ + var2->n2 + var0->_n2n3_) +
		var0to_n1n2_var1to_n1n2_->(var0->_n1n2_ + var1->_n1n2_) +
		var0to_n1n3_var2ton1var1to_n2n3_->(var0->_n1n3_ + var2->n1 + var1->_n2n3_) +
		var1to_n1n3_var2ton1var0to_n2n3_->(var1->_n1n3_ + var2->n1 + var0->_n2n3_) +
		var0to_n1n2_var1to_n1n2n3_->(var0->_n1n2_ + var1->_n1n2n3_) +
		var1to_n1n2_var0to_n1n2n3_->(var1->_n1n2_ + var0->_n1n2n3_) +
		var1to_n1n3_var0to_n1n3_var2ton1->(var1->_n1n3_ + var0->_n1n3_ + var2->n1) +
		var1to_n1n2n3_var0to_n1n2n3_->(var1->_n1n2n3_ + var0->_n1n2n3_) +
		var2ton3var0to_n2n3_var1to_n2n3_->(var2->n3 + var0->_n2n3_ + var1->_n2n3_) +
		var2ton1var0to_n2n3_var1to_n2n3_->(var2->n1 + var0->_n2n3_ + var1->_n2n3_) +
		var0to_n1n2_var1to_n2n3_->(var0->_n1n2_ + var1->_n2n3_) +
		var1to_n1n2_var0to_n2n3_->(var1->_n1n2_ + var0->_n2n3_) +
		var0to_n1n2_var1to_n1n2_var2ton1->(var0->_n1n2_ + var1->_n1n2_ + var2->n1) +
		var0to_n1n2n3_var1to_n2n3_->(var0->_n1n2n3_ + var1->_n2n3_) +
		var1to_n1n2n3_var0to_n2n3_->(var1->_n1n2n3_ + var0->_n2n3_) +
		var0to_n1n2_var1to_n1n2n3_var2ton1->(var0->_n1n2_ + var1->_n1n2n3_ + var2->n1) +
		var1to_n1n2_var0to_n1n2n3_var2ton1->(var1->_n1n2_ + var0->_n1n2n3_ + var2->n1) +
		var1to_n1n2n3_var0to_n1n2n3_var2ton1->(var1->_n1n2n3_ + var0->_n1n2n3_ + var2->n1) +
		var0to_n1n2_->(var0->_n1n2_) +
		var0to_n1n2n3_->(var0->_n1n2n3_) +
		var1to_n1n3_var0to_n1n3_var2ton2->(var1->_n1n3_ + var0->_n1n3_ + var2->n2) +
		var2ton3var0to_n1n3_var1to_n2n3_->(var2->n3 + var0->_n1n3_ + var1->_n2n3_) +
		var2ton3var1to_n1n3_var0to_n2n3_->(var2->n3 + var1->_n1n3_ + var0->_n2n3_) +
		var2ton3var1to_n1n2n3_var0to_n1n2n3_->(var2->n3 + var1->_n1n2n3_ + var0->_n1n2n3_) +
		var2ton3var0to_n1n2_var1to_n1n2n3_->(var2->n3 + var0->_n1n2_ + var1->_n1n2n3_) +
		var2ton3var1to_n1n2_var0to_n1n2n3_->(var2->n3 + var1->_n1n2_ + var0->_n1n2n3_) +
		var2ton3var0to_n1n2_var1to_n1n2_->(var2->n3 + var0->_n1n2_ + var1->_n1n2_) +
		var0to_n1n2_var2ton1var1to_n2n3_->(var0->_n1n2_ + var2->n1 + var1->_n2n3_) +
		var1to_n1n2_var2ton1var0to_n2n3_->(var1->_n1n2_ + var2->n1 + var0->_n2n3_) +
		var0to_n2n3_var1to_n2n3_->(var0->_n2n3_ + var1->_n2n3_) +
		var0to_n2n3_->(var0->_n2n3_)

	baseName = CommitEntryn2_n1n3_NUM1NUM2->CommitEntry +
		CommitEntryn1_n1n2_NUM1NUM2->CommitEntry +
		CommitEntryn1_n1n2_NUM1NUM1->CommitEntry +
		CommitEntryn2_n1n2_NUM1NUM0->CommitEntry +
		ClientRequestn1NUM1->ClientRequest +
		CommitEntryn2_n1n2_NUM1NUM2->CommitEntry +
		CommitEntryn1_n1n3_NUM2NUM1->CommitEntry +
		CommitEntryn1_n1n3_NUM2NUM2->CommitEntry +
		BecomeLeadern1_n1n2_NUM1->BecomeLeader +
		BecomeLeadern2_n1n2_NUM2->BecomeLeader +
		BecomeLeadern2_n2n3_NUM0->BecomeLeader +
		BecomeLeadern2_n2n3_NUM2->BecomeLeader +
		ClientRequestn2NUM0->ClientRequest +
		ClientRequestn2NUM2->ClientRequest +
		BecomeLeadern1_n1n2_NUM2->BecomeLeader +
		CommitEntryn1_n1n3_NUM1NUM1->CommitEntry
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT24 extends PosTrace {} {}
one sig PT25 extends PosTrace {} {}
one sig PT26 extends PosTrace {} {}
one sig PT27 extends PosTrace {} {}
one sig PT28 extends PosTrace {} {}
one sig PT29 extends PosTrace {} {}
one sig PT30 extends PosTrace {} {}
one sig PT31 extends PosTrace {} {}
one sig PT32 extends PosTrace {} {}
