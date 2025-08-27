//39
//9
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

    // constraints for improving speed, but sacrifice expressivity
    #flActions <= 3 // at most three total fluent actions
    #({a : flActions | a.value = True}) <= 2 // at most two True-valued fluent action
    #({a : flActions | a.value = False}) <= 2 // at most two False-valued fluent action

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

	// require lhs to not have have an Implies node
 // this is an overconstraint for improving speed
	all f : Implies | no (f.left.*children) & Implies

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
	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals
	minsome flActions // heuristic to synthesize the least complicated fluents as possible
	softno mutInitFluents // fewer mutex fluents
	softno partialFluents // fewer partial fluents
	minsome Fluent.vars // minimize the # of params for each fluent
}
for 9 Formula, 5 FlSymAction

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
	let containsRel = (NUM0->NUM0 + NUM0->NUM1 + NUM0->NUM2 + NUM0->NUM3 + NUM0->NUM4 + NUM1->NUM1 + NUM1->NUM2 + NUM1->NUM3 + NUM1->NUM4 + NUM2->NUM2 + NUM2->NUM3 + NUM2->NUM4 + NUM3->NUM3 + NUM3->NUM4 + NUM4->NUM4) |
		(lhs->rhs) in containsRel
}


one sig n1, n2, n3, _n2n3_, _n1n2n3_, NUM2, NUM3, NUM4, _n1n3_, _n1n2_, NUM0, NUM1 extends Atom {}

one sig FinNat extends Sort {} {
	atoms = NUM2 + NUM3 + NUM4 + NUM0 + NUM1
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

one sig RollbackEntries extends BaseName {} {
	paramIdxs = P0 + P1
	paramTypes = P0->Server + P1->Server
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
one sig GetEntriesn3n1 extends Act {} {
	params = (P0->n3 + P1->n1)
}

one sig BecomeLeader extends BaseName {} {
	paramIdxs = P0 + P1 + P2
	paramTypes = P0->Server + P1->Quorums + P2->FinNat
}
one sig BecomeLeadern1_n1n2n3_NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n2n3_ + P2->NUM1)
}
one sig BecomeLeadern2_n2n3_NUM2 extends Act {} {
	params = (P0->n2 + P1->_n2n3_ + P2->NUM2)
}
one sig BecomeLeadern1_n1n2_NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM1)
}
one sig BecomeLeadern1_n1n2_NUM2 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM2)
}
one sig BecomeLeadern1_n1n3_NUM3 extends Act {} {
	params = (P0->n1 + P1->_n1n3_ + P2->NUM3)
}

one sig CommitEntry extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3 + P4
	paramTypes = P0->Server + P1->Quorums + P2->FinNat + P3->FinNat + P4->FinNat
}
one sig CommitEntryn1_n1n2_NUM2NUM2NUM2 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM2 + P3->NUM2 + P4->NUM2)
}
one sig CommitEntryn1_n1n3_NUM1NUM1NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n3_ + P2->NUM1 + P3->NUM1 + P4->NUM1)
}
one sig CommitEntryn1_n1n3_NUM1NUM3NUM3 extends Act {} {
	params = (P0->n1 + P1->_n1n3_ + P2->NUM1 + P3->NUM3 + P4->NUM3)
}
one sig CommitEntryn1_n1n2_NUM1NUM1NUM1 extends Act {} {
	params = (P0->n1 + P1->_n1n2_ + P2->NUM1 + P3->NUM1 + P4->NUM1)
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


one sig T0, T1, T2, T3, T4, T5, T6 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6
	CommitEntry in FlSymAction.baseName // the final base name in the neg trace must appear in the sep formula
}


fun envVarTypes : set(Var->Sort) {
	var2->Server + var1->FinNat + var0->Server
}


one sig var2, var1, var0 extends Var {} {}


one sig var2ton3var0ton3var1toNUM4 extends Env {} {}
one sig var0ton3var2ton1var1toNUM2 extends Env {} {}
one sig var1toNUM3var0ton2var2ton1 extends Env {} {}
one sig var2ton3var1toNUM1var0ton2 extends Env {} {}
one sig var1toNUM4var0ton1var2ton1 extends Env {} {}
one sig var0ton1var1toNUM2 extends Env {} {}
one sig var1toNUM0var0ton3 extends Env {} {}
one sig var1toNUM1var0ton2 extends Env {} {}
one sig var0ton2var2ton2var1toNUM2 extends Env {} {}
one sig var2ton3var0ton1var1toNUM2 extends Env {} {}
one sig var2ton3var1toNUM0var0ton3 extends Env {} {}
one sig var1toNUM3var2ton2var0ton1 extends Env {} {}
one sig var0ton3var1toNUM1var2ton2 extends Env {} {}
one sig var1toNUM0var0ton1 extends Env {} {}
one sig var0ton2 extends Env {} {}
one sig var0ton3var1toNUM4var2ton1 extends Env {} {}
one sig var1toNUM3var0ton3var2ton2 extends Env {} {}
one sig var1toNUM4var0ton2var2ton2 extends Env {} {}
one sig var2ton3var0ton3var1toNUM2 extends Env {} {}
one sig var2ton3var1toNUM3var0ton2 extends Env {} {}
one sig var2ton3var1toNUM4var0ton1 extends Env {} {}
one sig var0ton3var1toNUM2 extends Env {} {}
one sig var1toNUM3var0ton2 extends Env {} {}
one sig var1toNUM4var0ton1 extends Env {} {}
one sig var0ton3 extends Env {} {}
one sig var0ton1var2ton1var1toNUM2 extends Env {} {}
one sig var1toNUM0var0ton3var2ton1 extends Env {} {}
one sig var1toNUM1var0ton2var2ton1 extends Env {} {}
one sig var1toNUM0var0ton2var2ton2 extends Env {} {}
one sig var1toNUM1var2ton2var0ton1 extends Env {} {}
one sig var2ton3var1toNUM0var0ton1 extends Env {} {}
one sig var1toNUM0var0ton1var2ton1 extends Env {} {}
one sig var0ton3var1toNUM4 extends Env {} {}
one sig var0ton3var1toNUM4var2ton2 extends Env {} {}
one sig var2ton3var1toNUM3var0ton3 extends Env {} {}
one sig var2ton3var1toNUM4var0ton2 extends Env {} {}
one sig var1toNUM0var0ton2 extends Env {} {}
one sig var1toNUM1var0ton1 extends Env {} {}
one sig var1toNUM3var0ton3var2ton1 extends Env {} {}
one sig var1toNUM4var0ton2var2ton1 extends Env {} {}
one sig var0ton3var2ton2var1toNUM2 extends Env {} {}
one sig var1toNUM3var0ton2var2ton2 extends Env {} {}
one sig var1toNUM4var2ton2var0ton1 extends Env {} {}
one sig var2ton3var0ton2var1toNUM2 extends Env {} {}
one sig var2ton3var1toNUM3var0ton1 extends Env {} {}
one sig var2ton3var0ton3var1toNUM1 extends Env {} {}
one sig var0ton1 extends Env {} {}
one sig var1toNUM3var0ton3 extends Env {} {}
one sig var1toNUM4var0ton2 extends Env {} {}
one sig var1toNUM0var0ton2var2ton1 extends Env {} {}
one sig var1toNUM1var0ton1var2ton1 extends Env {} {}
one sig var1toNUM0var2ton2var0ton1 extends Env {} {}
one sig var0ton2var2ton1var1toNUM2 extends Env {} {}
one sig var1toNUM3var0ton1var2ton1 extends Env {} {}
one sig var0ton3var1toNUM1var2ton1 extends Env {} {}
one sig var2ton2var0ton1var1toNUM2 extends Env {} {}
one sig var1toNUM0var0ton3var2ton2 extends Env {} {}
one sig var1toNUM1var0ton2var2ton2 extends Env {} {}
one sig var2ton3var1toNUM0var0ton2 extends Env {} {}
one sig var2ton3var1toNUM1var0ton1 extends Env {} {}
one sig var0ton2var1toNUM2 extends Env {} {}
one sig var1toNUM3var0ton1 extends Env {} {}
one sig var0ton3var1toNUM1 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT20->T2) + (PT5->T1) + (PT19->T3) + (PT15->T2) + (PT24->T4) + (PT1->T6) + (PT17->T2) + (PT21->T2) + (NT1->T6)

	path = (PT20 -> (T0->GetEntriesn1n1 + T1->BecomeLeadern1_n1n2_NUM1 + T2->CommitEntryn1_n1n2_NUM1NUM1NUM1)) +
		(PT5 -> (T0->BecomeLeadern1_n1n2n3_NUM1 + T1->CommitEntryn1_n1n2_NUM1NUM1NUM1)) +
		(PT19 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern1_n1n2_NUM2 + T3->CommitEntryn1_n1n2_NUM2NUM2NUM2)) +
		(PT15 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->CommitEntryn1_n1n2_NUM1NUM1NUM1 + T2->BecomeLeadern1_n1n2_NUM2)) +
		(PT24 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->CommitEntryn1_n1n2_NUM1NUM1NUM1 + T3->BecomeLeadern1_n1n2_NUM2 + T4->ClientRequestn1NUM2)) +
		(PT1 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->GetEntriesn3n1 + T5->BecomeLeadern1_n1n3_NUM3 + T6->CommitEntryn1_n1n3_NUM1NUM3NUM3)) +
		(PT17 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->GetEntriesn2n1 + T2->CommitEntryn1_n1n2_NUM1NUM1NUM1)) +
		(PT21 -> (T0->GetEntriesn2n1 + T1->BecomeLeadern1_n1n2_NUM1 + T2->CommitEntryn1_n1n2_NUM1NUM1NUM1)) +
		(NT1 -> (T0->BecomeLeadern1_n1n2_NUM1 + T1->ClientRequestn1NUM1 + T2->BecomeLeadern2_n2n3_NUM2 + T3->ClientRequestn2NUM2 + T4->GetEntriesn3n1 + T5->BecomeLeadern1_n1n3_NUM3 + T6->CommitEntryn1_n1n3_NUM1NUM1NUM1))

	maps = var2ton3var0ton3var1toNUM4->(var2->n3 + var0->n3 + var1->NUM4) +
		var0ton3var2ton1var1toNUM2->(var0->n3 + var2->n1 + var1->NUM2) +
		var1toNUM3var0ton2var2ton1->(var1->NUM3 + var0->n2 + var2->n1) +
		var1toNUM4var0ton1var2ton1->(var1->NUM4 + var0->n1 + var2->n1) +
		var0ton1var1toNUM2->(var0->n1 + var1->NUM2) +
		var1toNUM0var0ton3->(var1->NUM0 + var0->n3) +
		var1toNUM1var0ton2->(var1->NUM1 + var0->n2) +
		var0ton2var2ton2var1toNUM2->(var0->n2 + var2->n2 + var1->NUM2) +
		var2ton3var0ton1var1toNUM2->(var2->n3 + var0->n1 + var1->NUM2) +
		var1toNUM3var2ton2var0ton1->(var1->NUM3 + var2->n2 + var0->n1) +
		var0ton3var1toNUM1var2ton2->(var0->n3 + var1->NUM1 + var2->n2) +
		var2ton3var1toNUM1var0ton2->(var2->n3 + var1->NUM1 + var0->n2) +
		var2ton3var1toNUM0var0ton3->(var2->n3 + var1->NUM0 + var0->n3) +
		var1toNUM0var0ton1->(var1->NUM0 + var0->n1) +
		var0ton2->(var0->n2) +
		var0ton3var1toNUM4var2ton1->(var0->n3 + var1->NUM4 + var2->n1) +
		var1toNUM3var0ton3var2ton2->(var1->NUM3 + var0->n3 + var2->n2) +
		var1toNUM4var0ton2var2ton2->(var1->NUM4 + var0->n2 + var2->n2) +
		var2ton3var0ton3var1toNUM2->(var2->n3 + var0->n3 + var1->NUM2) +
		var2ton3var1toNUM3var0ton2->(var2->n3 + var1->NUM3 + var0->n2) +
		var2ton3var1toNUM4var0ton1->(var2->n3 + var1->NUM4 + var0->n1) +
		var0ton3var1toNUM2->(var0->n3 + var1->NUM2) +
		var1toNUM3var0ton2->(var1->NUM3 + var0->n2) +
		var1toNUM4var0ton1->(var1->NUM4 + var0->n1) +
		var0ton3->(var0->n3) +
		var0ton1var2ton1var1toNUM2->(var0->n1 + var2->n1 + var1->NUM2) +
		var1toNUM0var0ton3var2ton1->(var1->NUM0 + var0->n3 + var2->n1) +
		var1toNUM1var0ton2var2ton1->(var1->NUM1 + var0->n2 + var2->n1) +
		var1toNUM0var0ton2var2ton2->(var1->NUM0 + var0->n2 + var2->n2) +
		var1toNUM1var2ton2var0ton1->(var1->NUM1 + var2->n2 + var0->n1) +
		var2ton3var1toNUM0var0ton1->(var2->n3 + var1->NUM0 + var0->n1) +
		var1toNUM0var0ton1var2ton1->(var1->NUM0 + var0->n1 + var2->n1) +
		var0ton3var1toNUM4->(var0->n3 + var1->NUM4) +
		var0ton3var1toNUM4var2ton2->(var0->n3 + var1->NUM4 + var2->n2) +
		var2ton3var1toNUM3var0ton3->(var2->n3 + var1->NUM3 + var0->n3) +
		var2ton3var1toNUM4var0ton2->(var2->n3 + var1->NUM4 + var0->n2) +
		var1toNUM0var0ton2->(var1->NUM0 + var0->n2) +
		var1toNUM1var0ton1->(var1->NUM1 + var0->n1) +
		var1toNUM3var0ton3var2ton1->(var1->NUM3 + var0->n3 + var2->n1) +
		var1toNUM4var0ton2var2ton1->(var1->NUM4 + var0->n2 + var2->n1) +
		var0ton3var2ton2var1toNUM2->(var0->n3 + var2->n2 + var1->NUM2) +
		var1toNUM3var0ton2var2ton2->(var1->NUM3 + var0->n2 + var2->n2) +
		var1toNUM4var2ton2var0ton1->(var1->NUM4 + var2->n2 + var0->n1) +
		var2ton3var0ton2var1toNUM2->(var2->n3 + var0->n2 + var1->NUM2) +
		var2ton3var1toNUM3var0ton1->(var2->n3 + var1->NUM3 + var0->n1) +
		var2ton3var0ton3var1toNUM1->(var2->n3 + var0->n3 + var1->NUM1) +
		var0ton1->(var0->n1) +
		var1toNUM3var0ton3->(var1->NUM3 + var0->n3) +
		var1toNUM4var0ton2->(var1->NUM4 + var0->n2) +
		var1toNUM0var0ton2var2ton1->(var1->NUM0 + var0->n2 + var2->n1) +
		var1toNUM1var0ton1var2ton1->(var1->NUM1 + var0->n1 + var2->n1) +
		var1toNUM0var2ton2var0ton1->(var1->NUM0 + var2->n2 + var0->n1) +
		var0ton2var2ton1var1toNUM2->(var0->n2 + var2->n1 + var1->NUM2) +
		var1toNUM3var0ton1var2ton1->(var1->NUM3 + var0->n1 + var2->n1) +
		var0ton3var1toNUM1var2ton1->(var0->n3 + var1->NUM1 + var2->n1) +
		var2ton2var0ton1var1toNUM2->(var2->n2 + var0->n1 + var1->NUM2) +
		var1toNUM0var0ton3var2ton2->(var1->NUM0 + var0->n3 + var2->n2) +
		var1toNUM1var0ton2var2ton2->(var1->NUM1 + var0->n2 + var2->n2) +
		var2ton3var1toNUM0var0ton2->(var2->n3 + var1->NUM0 + var0->n2) +
		var2ton3var1toNUM1var0ton1->(var2->n3 + var1->NUM1 + var0->n1) +
		var0ton2var1toNUM2->(var0->n2 + var1->NUM2) +
		var1toNUM3var0ton1->(var1->NUM3 + var0->n1) +
		var0ton3var1toNUM1->(var0->n3 + var1->NUM1)

	baseName = CommitEntryn1_n1n3_NUM1NUM3NUM3->CommitEntry +
		BecomeLeadern1_n1n3_NUM3->BecomeLeader +
		ClientRequestn1NUM1->ClientRequest +
		CommitEntryn1_n1n2_NUM2NUM2NUM2->CommitEntry +
		CommitEntryn1_n1n3_NUM1NUM1NUM1->CommitEntry +
		ClientRequestn1NUM2->ClientRequest +
		BecomeLeadern1_n1n2n3_NUM1->BecomeLeader +
		BecomeLeadern1_n1n2_NUM1->BecomeLeader +
		BecomeLeadern2_n2n3_NUM2->BecomeLeader +
		CommitEntryn1_n1n2_NUM1NUM1NUM1->CommitEntry +
		GetEntriesn2n1->GetEntries +
		ClientRequestn2NUM2->ClientRequest +
		GetEntriesn1n1->GetEntries +
		GetEntriesn3n1->GetEntries +
		BecomeLeadern1_n1n2_NUM2->BecomeLeader
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT20 extends PosTrace {} {}
one sig PT5 extends PosTrace {} {}
one sig PT19 extends PosTrace {} {}
one sig PT15 extends PosTrace {} {}
one sig PT24 extends PosTrace {} {}
one sig PT1 extends PosTrace {} {}
one sig PT17 extends PosTrace {} {}
one sig PT21 extends PosTrace {} {}
