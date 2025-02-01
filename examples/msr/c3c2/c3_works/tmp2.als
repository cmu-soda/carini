//13
//0
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

    // strong condition for ensuring each fluent category is mutex
    no initFl & termFl
    no initFl & mutInitFl
    no initFl & falsifyFl
    no termFl & mutInitFl
    no termFl & falsifyFl
    no mutInitFl & falsifyFl
    all fl1,fl2 : (initFl+termFl+mutInitFl+falsifyFl) | (fl1.baseName & fl2.baseName != none) implies fl1 = fl2
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

    //no falsifyFl.actToFlParamsMap // falsify fluents don't take params

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
	Fluent.(initFl+termFl+mutInitFl+falsifyFl) = FlSymAction // all FlSymActions must be in fluents

	// no free vars, all vars must be used in the matrix
	let varsInMatrix = ParamIdx.(Fluent.vars) + VarEquals.(lhs+rhs) + VarSetContains.(elem+theSet) + VarLTE.(lhs+rhs) |
		varsInMatrix = (Forall.var + Exists.var)

	// do not quantify over a variable that's already in scope
	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)

	// speed optimization: require lhs to not have have an Implies node
	// we declare this here (instead of in Implies) because referring to 'children'
	// results in an error (due to weird scoping).
	all f : Implies | (f.left).*children not in Implies

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
	//all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies
	//all pt : (PT2068+PT511) | EmptyEnv->indices[pt]->Root in pt.satisfies
	all nt : NegTrace | no (EmptyEnv->nt.lastIdx->Root & nt.satisfies)
	EmptyEnv->T0->Root in EmptyTrace.satisfies // the formula must satisfy the empty trace
	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals
	minsome initFl + termFl + mutInitFl + falsifyFl // heuristic to synthesize the least complicated fluents as possible
	softno mutInitFl + falsifyFl // prefer initFl and termFl over mutInitFl and falsifyFl
	minsome Fluent.vars // minimize the # of params for each fluent
}
for 9 Formula, 6 FlSymAction

fact {
    Root.children.children in Forall
    Root.children.children.children in Implies
    Root.children.children.children.left in Fluent
    Root.children.children.children.left.mutInitFl.baseName = BecomeLeader
    Root.children.children.children.right in Implies
    Root.children.children.children.right.left in Fluent
    Root.children.children.children.right.left.initFl.baseName = CommitEntry
    Root.children.children.children.right.left.falsifyFl.baseName = BecomeLeader
    Root.children.children.children.right.right in VarEquals
    //some falsifyFl
}

one sig P0, P1, P2, P3, P4 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = P0->P1 + P1->P2 + P2->P3 + P3->P4
	all f : Fluent | (f.vars.Var = P0) or (f.vars.Var = P0+P1) or (f.vars.Var = P0+P1+P2) or (f.vars.Var = P0+P1+P2+P3) or (f.vars.Var = P0+P1+P2+P3+P4)
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

one sig Server extends Sort {} {
	atoms = n1 + n2 + n3
	numericSort = False
}
one sig Quorums extends Sort {} {
	atoms = _n2n3_ + _n1n2n3_ + _n1n3_ + _n1n2_
	numericSort = False
}
one sig FinNat extends Sort {} {
	atoms = NUM2 + NUM3 + NUM0 + NUM1
	numericSort = True
}

one sig RollbackEntries extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Server + P1->Server
}
one sig RollbackEntriesn3n2 extends Act {} {
	params = (P0->n3 + P1->n2)
}

one sig GetEntries extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Server + P1->Server
}
one sig GetEntriesn1n1 extends Act {} {
	params = (P0->n1 + P1->n1)
}
one sig GetEntriesn2n1 extends Act {} {
	params = (P0->n2 + P1->n1)
}
one sig GetEntriesn3n2 extends Act {} {
	params = (P0->n3 + P1->n2)
}
one sig GetEntriesn3n1 extends Act {} {
	params = (P0->n3 + P1->n1)
}

one sig BecomeLeader extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Server + P1->Quorums + P2->FinNat
}
one sig BecomeLeadern2_n1n2n3_NUM2 extends Act {} {
	params = (P0->n2 + P1->_n1n2n3_ + P2->NUM2)
}
one sig BecomeLeadern2_n1n2n3_NUM3 extends Act {} {
	params = (P0->n2 + P1->_n1n2n3_ + P2->NUM3)
}
one sig BecomeLeadern3_n1n2n3_NUM3 extends Act {} {
	params = (P0->n3 + P1->_n1n2n3_ + P2->NUM3)
}
one sig BecomeLeadern2_n2n3_NUM2 extends Act {} {
	params = (P0->n2 + P1->_n2n3_ + P2->NUM2)
}
one sig BecomeLeadern2_n2n3_NUM3 extends Act {} {
	params = (P0->n2 + P1->_n2n3_ + P2->NUM3)
}
one sig BecomeLeadern3_n2n3_NUM3 extends Act {} {
	params = (P0->n3 + P1->_n2n3_ + P2->NUM3)
}
one sig BecomeLeadern1_n1n3_NUM2 extends Act {} {
	params = (P0->n1 + P1->_n1n3_ + P2->NUM2)
}
one sig BecomeLeadern2_n1n2_NUM2 extends Act {} {
	params = (P0->n2 + P1->_n1n2_ + P2->NUM2)
}
one sig BecomeLeadern1_n1n2_NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM1)
}
one sig BecomeLeadern1_n1n3_NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n3_ + P2->NUM1)
}
one sig BecomeLeadern1_n1n2_NUM2 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM2)
}

one sig CommitEntry extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3 + P4
	paramTypes = P0->Server + P1->Quorums + P2->FinNat + P3->FinNat + P4->FinNat
}
one sig CommitEntryn2_n2n3_NUM1NUM2NUM2 extends Act {} {
	params = (P0->n2 + P1->_n2n3_ + P2->NUM1 + P3->NUM2 + P4->NUM2)
}
one sig CommitEntryn1_n1n2_NUM1NUM2NUM2 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM1 + P3->NUM2 + P4->NUM2)
}
one sig CommitEntryn1_n1n2_NUM1NUM1NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM1 + P3->NUM1 + P4->NUM1)
}
one sig CommitEntryn1_n1n2_NUM2NUM2NUM2 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM2 + P3->NUM2 + P4->NUM2)
}
one sig CommitEntryn1_n1n3_NUM1NUM1NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n3_ + P2->NUM1 + P3->NUM1 + P4->NUM1)
}
one sig CommitEntryn1_n1n2_NUM2NUM1NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM2 + P3->NUM1 + P4->NUM1)
}
one sig CommitEntryn2_n1n3_NUM1NUM2NUM2 extends Act {} {
	params = (P0->n2 + P1->_n1n3_ + P2->NUM1 + P3->NUM2 + P4->NUM2)
}

one sig ClientRequest extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Server + P1->FinNat
}
one sig ClientRequestn1NUM2 extends Act {} {
	params = (P0->n1 + P1->NUM2)
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
	CommitEntry in FlSymAction.baseName // the final base name in the neg trace must appear in the sep formula

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
one sig var2ton3var0toNUM1var1toNUM1 extends Env {} {}
one sig var2ton3var0toNUM0var1toNUM2 extends Env {} {}
one sig var2ton3var1toNUM0var0toNUM2 extends Env {} {}
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
one sig var0toNUM0var2ton2var1toNUM2 extends Env {} {}
one sig var0toNUM1var2ton1var1toNUM2 extends Env {} {}
one sig var1toNUM3var0toNUM0var2ton1 extends Env {} {}
one sig var0toNUM3var1toNUM0var2ton1 extends Env {} {}
one sig var1toNUM1var0toNUM2var2ton1 extends Env {} {}
one sig var1toNUM0var2ton2var0toNUM2 extends Env {} {}
one sig var0toNUM1var1toNUM1var2ton2 extends Env {} {}
one sig var2ton3var1toNUM0var0toNUM1 extends Env {} {}
one sig var2ton3var0toNUM0var1toNUM1 extends Env {} {}
one sig var2ton2var0toNUM2var1toNUM2 extends Env {} {}
one sig var0toNUM3var2ton1var1toNUM2 extends Env {} {}
one sig var1toNUM3var0toNUM2var2ton1 extends Env {} {}
one sig var1toNUM3var0toNUM1var2ton2 extends Env {} {}
one sig var0toNUM3var1toNUM1var2ton2 extends Env {} {}
one sig var2ton3var0toNUM1var1toNUM2 extends Env {} {}
one sig var2ton3var1toNUM3var0toNUM0 extends Env {} {}
one sig var2ton3var0toNUM3var1toNUM0 extends Env {} {}
one sig var2ton3var1toNUM1var0toNUM2 extends Env {} {}


fact PartialInstance {
	//lastIdx = (EmptyTrace->T0) + (PT239->T2) + (PT504->T2) + (PT511->T2) + (PT505->T3) + (PT114->T2) + (PT243->T3) + (PT1->T0) + (PT1035->T4) + (PT1032->T3) + (PT508->T3) + (PT241->T4) + (PT247->T3) + (PT509->T2) + (PT1033->T2) + (PT510->T2) + (PT107->T2) + (PT1017->T5) + (PT2079->T5) + (PT95->T5) + (PT2072->T5) + (PT2070->T5) + (PT2068->T5) + (NT1->T5)
	lastIdx = (EmptyTrace->T0) + (PT511->T2) + (PT2068->T5) + (NT1->T5)

	path = //(PT239 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->CommitEntryn1_n1n2_NUM1NUM1NUM1 + T2->BecomeLeadern2_n1n2_NUM2)) +
		//(PT504 -> (T0->GetEntriesn1n1 + T1->GetEntriesn2n1 + T2->GetEntriesn3n1)) +
		(PT511 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->CommitEntryn1_n1n2_NUM2NUM1NUM1)) +
		//(PT505 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern1_n1n2_NUM2 + T3->CommitEntryn1_n1n2_NUM2NUM2NUM2)) +
		//(PT114 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->CommitEntryn1_n1n2_NUM1NUM1NUM1 + T2->BecomeLeadern1_n1n2_NUM2)) +
		//(PT243 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern1_n1n2_NUM2 + T3->CommitEntryn1_n1n2_NUM1NUM2NUM2)) +
		//(PT1 -> (T0->BecomeLeadern1_n1n3_NUM1)) +
		//(PT1035 -> (T0->GetEntriesn1n1 + T1->GetEntriesn2n1 + T2->GetEntriesn3n2 + T3->BecomeLeadern1_n1n2_NUM1 + T4->CommitEntryn1_n1n2_NUM1NUM1NUM1)) +
		//(PT1032 -> (T0->GetEntriesn2n1 + T1->BecomeLeadern1_n1n2_NUM1 + T2->ClientRequestn1NUM1 + T3->CommitEntryn1_n1n2_NUM1NUM1NUM1)) +
		//(PT508 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->BecomeLeadern2_n2n3_NUM2 + T2->ClientRequestn1NUM1 + T3->CommitEntryn2_n2n3_NUM1NUM2NUM2)) +
		//(PT241 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->CommitEntryn1_n1n2_NUM1NUM1NUM1 + T3->BecomeLeadern1_n1n2_NUM2 + T4->ClientRequestn1NUM2)) +
		//(PT247 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n1n2n3_NUM2 + T3->CommitEntryn2_n1n3_NUM1NUM2NUM2)) +
		//(PT509 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->BecomeLeadern1_n1n3_NUM2 + T2->BecomeLeadern3_n2n3_NUM3)) +
		//(PT1033 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->CommitEntryn1_n1n2_NUM1NUM1NUM1 + T2->BecomeLeadern2_n2n3_NUM2)) +
		//(PT510 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->GetEntriesn2n1 + T2->CommitEntryn1_n1n2_NUM1NUM1NUM1)) +
		//(PT107 -> (T0->GetEntriesn2n1 + T1->BecomeLeadern1_n1n2_NUM1 + T2->CommitEntryn1_n1n2_NUM1NUM1NUM1)) +
		//(PT1017 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->GetEntriesn3n1 + T5->BecomeLeadern2_n1n2n3_NUM3)) +
		//(PT2079 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->GetEntriesn3n1 + T5->BecomeLeadern2_n2n3_NUM3)) +
		//(PT95 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->GetEntriesn3n1 + T5->RollbackEntriesn3n2)) +
		//(PT2072 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->GetEntriesn3n1 + T5->RollbackEntriesn3n2)) +
		//(PT2070 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->GetEntriesn3n1 + T5->BecomeLeadern3_n1n2n3_NUM3)) +
		(PT2068 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->GetEntriesn3n1 + T5->ClientRequestn1NUM1)) +
		(NT1 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->GetEntriesn3n1 + T5->CommitEntryn1_n1n3_NUM1NUM1NUM1))

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
		var1toNUM1var2ton2var0toNUM2->(var1->NUM1 + var2->n2 + var0->NUM2) +
		var0toNUM2var2ton1var1toNUM2->(var0->NUM2 + var2->n1 + var1->NUM2) +
		var1toNUM3var0toNUM1var2ton1->(var1->NUM3 + var0->NUM1 + var2->n1) +
		var0toNUM3var1toNUM1var2ton1->(var0->NUM3 + var1->NUM1 + var2->n1) +
		var0toNUM1var2ton2var1toNUM2->(var0->NUM1 + var2->n2 + var1->NUM2) +
		var1toNUM3var0toNUM0var2ton2->(var1->NUM3 + var0->NUM0 + var2->n2) +
		var0toNUM3var1toNUM0var2ton2->(var0->NUM3 + var1->NUM0 + var2->n2) +
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
		var0toNUM3var1toNUM0var2ton1->(var0->NUM3 + var1->NUM0 + var2->n1) +
		var0toNUM1var2ton1var1toNUM2->(var0->NUM1 + var2->n1 + var1->NUM2) +
		var1toNUM3var0toNUM0var2ton1->(var1->NUM3 + var0->NUM0 + var2->n1) +
		var1toNUM1var0toNUM2var2ton1->(var1->NUM1 + var0->NUM2 + var2->n1) +
		var0toNUM0var2ton2var1toNUM2->(var0->NUM0 + var2->n2 + var1->NUM2) +
		var1toNUM0var2ton2var0toNUM2->(var1->NUM0 + var2->n2 + var0->NUM2) +
		var0toNUM1var1toNUM1var2ton2->(var0->NUM1 + var1->NUM1 + var2->n2) +
		var2ton3var1toNUM0var0toNUM1->(var2->n3 + var1->NUM0 + var0->NUM1) +
		var2ton3var0toNUM0var1toNUM1->(var2->n3 + var0->NUM0 + var1->NUM1) +
		var0toNUM3var2ton1var1toNUM2->(var0->NUM3 + var2->n1 + var1->NUM2) +
		var1toNUM3var0toNUM2var2ton1->(var1->NUM3 + var0->NUM2 + var2->n1) +
		var2ton2var0toNUM2var1toNUM2->(var2->n2 + var0->NUM2 + var1->NUM2) +
		var1toNUM3var0toNUM1var2ton2->(var1->NUM3 + var0->NUM1 + var2->n2) +
		var0toNUM3var1toNUM1var2ton2->(var0->NUM3 + var1->NUM1 + var2->n2) +
		var2ton3var0toNUM1var1toNUM2->(var2->n3 + var0->NUM1 + var1->NUM2) +
		var2ton3var1toNUM3var0toNUM0->(var2->n3 + var1->NUM3 + var0->NUM0) +
		var2ton3var0toNUM3var1toNUM0->(var2->n3 + var0->NUM3 + var1->NUM0) +
		var2ton3var1toNUM1var0toNUM2->(var2->n3 + var1->NUM1 + var0->NUM2)

	baseName = BecomeLeadern2_n1n2n3_NUM2->BecomeLeader +
		ClientRequestn1NUM1->ClientRequest +
		BecomeLeadern2_n1n2n3_NUM3->BecomeLeader +
		BecomeLeadern3_n1n2n3_NUM3->BecomeLeader +
		CommitEntryn1_n1n3_NUM1NUM1NUM1->CommitEntry +
		ClientRequestn1NUM2->ClientRequest +
		BecomeLeadern1_n1n3_NUM1->BecomeLeader +
		BecomeLeadern1_n1n3_NUM2->BecomeLeader +
		CommitEntryn2_n1n3_NUM1NUM2NUM2->CommitEntry +
		BecomeLeadern1_n1n2_NUM1->BecomeLeader +
		CommitEntryn2_n2n3_NUM1NUM2NUM2->CommitEntry +
		BecomeLeadern2_n2n3_NUM2->BecomeLeader +
		BecomeLeadern2_n2n3_NUM3->BecomeLeader +
		BecomeLeadern1_n1n2_NUM2->BecomeLeader +
		CommitEntryn1_n1n2_NUM2NUM2NUM2->CommitEntry +
		RollbackEntriesn3n2->RollbackEntries +
		BecomeLeadern2_n1n2_NUM2->BecomeLeader +
		CommitEntryn1_n1n2_NUM1NUM2NUM2->CommitEntry +
		CommitEntryn1_n1n2_NUM1NUM1NUM1->CommitEntry +
		GetEntriesn2n1->GetEntries +
		ClientRequestn2NUM2->ClientRequest +
		GetEntriesn1n1->GetEntries +
		CommitEntryn1_n1n2_NUM2NUM1NUM1->CommitEntry +
		GetEntriesn3n2->GetEntries +
		GetEntriesn3n1->GetEntries +
		BecomeLeadern3_n2n3_NUM3->BecomeLeader
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

//one sig PT239 extends PosTrace {} {}
//one sig PT504 extends PosTrace {} {}
one sig PT511 extends PosTrace {} {}
//one sig PT505 extends PosTrace {} {}
//one sig PT114 extends PosTrace {} {}
//one sig PT243 extends PosTrace {} {}
//one sig PT1 extends PosTrace {} {}
//one sig PT1035 extends PosTrace {} {}
//one sig PT1032 extends PosTrace {} {}
//one sig PT508 extends PosTrace {} {}
//one sig PT241 extends PosTrace {} {}
//one sig PT247 extends PosTrace {} {}
//one sig PT509 extends PosTrace {} {}
//one sig PT1033 extends PosTrace {} {}
//one sig PT510 extends PosTrace {} {}
//one sig PT107 extends PosTrace {} {}
//one sig PT1017 extends PosTrace {} {}
//one sig PT2079 extends PosTrace {} {}
//one sig PT95 extends PosTrace {} {}
//one sig PT2072 extends PosTrace {} {}
//one sig PT2070 extends PosTrace {} {}
one sig PT2068 extends PosTrace {} {}
