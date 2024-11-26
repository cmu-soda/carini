//14
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
    all k1,k2,v : ParamIdx | (k1->v in actToFlParamsMap and k2->v in actToFlParamsMap) implies (k1 = k2)
}

sig Fluent extends Formula {
    initially : Bool,
    initFl : set FlSymAction,
    termFl : set FlSymAction,

    // vars represents the parameters (including the ordering) to the fluent itself
    vars : set(ParamIdx->Var)
} {
    no children
    no initFl & termFl // ensures initFl and termFl are mutex
    some initFl + termFl
    some vars

    // vars is a function
    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)

    // each fluent must accept all the fluent params in vars
    all s : (initFl + termFl) | ParamIdx.(s.actToFlParamsMap) = vars.Var

    // each action must input the same param-types to the fluent
    let flParamTypes = vars.envVarTypes |
        all a : (initFl+termFl) |
            // for each param in the action, its type must match the fluent
            all actIdx : a.actToFlParamsMap.ParamIdx |
                let flIdx = actIdx.(a.actToFlParamsMap) |
                    flIdx.flParamTypes = actIdx.(a.baseName.paramTypes)

    // actToFlParamsMap is an injective function
    // furthermore, when we combine actToFlParamsMap across all actions, the combination
    // must STILL be injective
    all x1,x2,y1,y2 : ParamIdx |
        (x1->y1 in (initFl+termFl).actToFlParamsMap and x2->y2 in (initFl+termFl).actToFlParamsMap) implies (x1->y1 = x2->y2 or (not x1=x2 and not y1=y2))

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
	// 1. i = 0 and f.initally = True and t[i] \notin f.termFl
	// 2. t[i] \in f.initFl
	// 3. t[i] \notin f.termFl and (e |- t,i-1 |= f)
	all e : Env, i : Idx, f : Fluent | e->i->f in satisfies iff
        // a is the action at the current index i in the trace
        let a = i.path |
            ((i = IdxOrder/first and f.initially = True and not isTermAct[a,e,f]) or
             (isInitAct[a,e,f]) or
             (not isTermAct[a,e,f] and some i' : Idx | i'->i in IdxOrder/next and e->i'->f in satisfies))

	all e : Env, i : Idx, f : Forall | e->i->f in satisfies iff
		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Exists | e->i->f in satisfies iff
		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Root | e->i->f in satisfies iff e->i->f.children in satisfies
}

// does this action initiate the fluent?
pred isInitAct[a : Act, e : Env, f : Fluent] {
    some s : f.initFl |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps
}

// does this action terminate the fluent?
pred isTermAct[a : Act, e : Env, f : Fluent] {
    some s : f.termFl |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps
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
	minsome initFl + termFl // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent // fewer fluents makes local inductive invariant inference easier
}
for 9 Formula, 5 FlSymAction

one sig P0, P1, P2, P3, P4 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = P0->P1 + P1->P2 + P2->P3 + P3->P4
	all f : Fluent | (f.vars.Var = P0) or (f.vars.Var = P0+P1) or (f.vars.Var = P0+P1+P2) or (f.vars.Var = P0+P1+P2+P3) or (f.vars.Var = P0+P1+P2+P3+P4)
}



one sig n1, n2, n3 extends Atom {}

one sig Node extends Sort {} {
	atoms = n1 + n2 + n3
}

one sig Forward extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3 + P4
	paramTypes = P0->Node + P1->Node + P2->Node + P3->Node + P4->Node
}
one sig Forwardn2n1n2n2n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn2n1n2n2n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn2n1n2n2n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn1n1n3n1n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn1n1n3n1n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn1n1n3n1n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn1n1n1n1n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn1n1n2n3n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn1n1n2n3n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn1n1n1n1n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn1n1n2n3n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn1n1n1n1n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn1n1n2n2n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn1n1n2n2n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn1n1n2n2n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn1n1n2n1n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn1n1n2n1n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n1 + P4->n1)
}
one sig Forwardn1n1n3n2n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn1n1n3n2n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn1n1n1n3n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn1n1n1n3n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn1n1n1n2n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn1n1n1n2n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn1n1n1n2n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n2 + P4->n2)
}


one sig T0, T1, T2, T3 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3

}


fun envVarTypes : set(Var->Sort) {
	var2->Node + var1->Node + var0->Node
}


one sig var2, var1, var0 extends Var {} {}


one sig var0ton1var1ton1var2ton1 extends Env {} {}
one sig var0ton3var1ton2 extends Env {} {}
one sig var1ton3var0ton2 extends Env {} {}
one sig var0ton3var1ton3 extends Env {} {}
one sig var0ton3var1ton3var2ton1 extends Env {} {}
one sig var0ton3var1ton2var2ton2 extends Env {} {}
one sig var1ton3var0ton2var2ton2 extends Env {} {}
one sig var2ton3var0ton3var1ton1 extends Env {} {}
one sig var2ton3var0ton2var1ton2 extends Env {} {}
one sig var2ton3var1ton3var0ton1 extends Env {} {}
one sig var0ton3var1ton2var2ton1 extends Env {} {}
one sig var1ton3var0ton2var2ton1 extends Env {} {}
one sig var0ton3var2ton2var1ton1 extends Env {} {}
one sig var0ton2var1ton2var2ton2 extends Env {} {}
one sig var1ton3var2ton2var0ton1 extends Env {} {}
one sig var2ton3var0ton2var1ton1 extends Env {} {}
one sig var2ton3var1ton2var0ton1 extends Env {} {}
one sig var0ton3var1ton1var2ton1 extends Env {} {}
one sig var0ton2var1ton2var2ton1 extends Env {} {}
one sig var1ton3var0ton1var2ton1 extends Env {} {}
one sig var0ton2 extends Env {} {}
one sig var0ton2var2ton2var1ton1 extends Env {} {}
one sig var1ton2var2ton2var0ton1 extends Env {} {}
one sig var2ton3var0ton1var1ton1 extends Env {} {}
one sig var0ton2var1ton1var2ton1 extends Env {} {}
one sig var1ton2var0ton1var2ton1 extends Env {} {}
one sig var0ton1 extends Env {} {}
one sig var2ton2var0ton1var1ton1 extends Env {} {}
one sig var2ton3var0ton3var1ton3 extends Env {} {}
one sig var0ton3 extends Env {} {}
one sig var0ton3var1ton3var2ton2 extends Env {} {}
one sig var2ton3var0ton3var1ton2 extends Env {} {}
one sig var2ton3var1ton3var0ton2 extends Env {} {}
one sig var0ton3var1ton1 extends Env {} {}
one sig var0ton2var1ton2 extends Env {} {}
one sig var1ton3var0ton1 extends Env {} {}
one sig var0ton1var1ton1 extends Env {} {}
one sig var0ton2var1ton1 extends Env {} {}
one sig var1ton2var0ton1 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT172->T2) + (PT179->T2) + (PT182->T3) + (PT166->T3) + (PT175->T3) + (PT183->T2) + (PT168->T3) + (PT184->T3) + (PT187->T3) + (PT191->T3) + (PT190->T3) + (PT169->T3) + (PT176->T2) + (PT188->T2) + (PT171->T2) + (PT186->T3) + (PT192->T2) + (PT178->T3) + (PT180->T3) + (PT185->T3) + (PT170->T1) + (PT181->T2) + (PT177->T3) + (PT167->T2) + (PT189->T3) + (PT173->T3) + (PT174->T3) + (NT1->T3)

	path = (PT172 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n3n2)) +
		(PT179 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n2n2)) +
		(PT182 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n2n1 + T3->Forwardn1n1n2n2n2)) +
		(PT166 -> (T0->Forwardn1n1n1n1n1 + T1->Forwardn1n1n1n1n2 + T2->Forwardn1n1n1n2n3 + T3->Forwardn1n1n2n2n1)) +
		(PT175 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n2n1 + T3->Forwardn1n1n2n1n2)) +
		(PT183 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n2n3)) +
		(PT168 -> (T0->Forwardn1n1n1n1n1 + T1->Forwardn1n1n1n3n2 + T2->Forwardn1n1n3n2n1 + T3->Forwardn1n1n2n1n2)) +
		(PT184 -> (T0->Forwardn1n1n1n1n1 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n3n3 + T3->Forwardn1n1n3n1n1)) +
		(PT187 -> (T0->Forwardn1n1n1n1n3 + T1->Forwardn1n1n1n2n1 + T2->Forwardn1n1n2n3n1 + T3->Forwardn1n1n3n2n1)) +
		(PT191 -> (T0->Forwardn1n1n1n1n3 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n3n1 + T3->Forwardn1n1n3n2n1)) +
		(PT190 -> (T0->Forwardn1n1n1n1n1 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n3n1 + T3->Forwardn1n1n3n2n3)) +
		(PT169 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n1n1 + T3->Forwardn1n1n2n1n2)) +
		(PT176 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n1 + T2->Forwardn1n1n2n1n2)) +
		(PT188 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n3 + T2->Forwardn1n1n2n3n1)) +
		(PT171 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n1 + T2->Forwardn1n1n2n2n2)) +
		(PT186 -> (T0->Forwardn1n1n1n1n1 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n2n1 + T3->Forwardn1n1n2n2n3)) +
		(PT192 -> (T0->Forwardn2n1n2n2n1 + T1->Forwardn2n1n2n2n2 + T2->Forwardn2n1n2n2n3)) +
		(PT178 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n3n1 + T2->Forwardn1n1n3n2n1 + T3->Forwardn1n1n2n1n2)) +
		(PT180 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n1n1 + T3->Forwardn1n1n2n2n2)) +
		(PT185 -> (T0->Forwardn1n1n1n1n1 + T1->Forwardn1n1n1n2n1 + T2->Forwardn1n1n1n2n2 + T3->Forwardn1n1n2n3n3)) +
		(PT170 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn2n1n2n2n2)) +
		(PT181 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n3n1 + T2->Forwardn1n1n3n1n1)) +
		(PT177 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n3n1 + T3->Forwardn1n1n3n1n3)) +
		(PT167 -> (T0->Forwardn1n1n1n1n2 + T1->Forwardn1n1n1n2n1 + T2->Forwardn1n1n1n3n1)) +
		(PT189 -> (T0->Forwardn1n1n1n1n1 + T1->Forwardn1n1n1n2n1 + T2->Forwardn1n1n2n3n2 + T3->Forwardn1n1n3n2n3)) +
		(PT173 -> (T0->Forwardn1n1n1n1n1 + T1->Forwardn1n1n1n2n2 + T2->Forwardn1n1n2n3n2 + T3->Forwardn1n1n3n1n2)) +
		(PT174 -> (T0->Forwardn1n1n1n1n3 + T1->Forwardn1n1n1n3n1 + T2->Forwardn1n1n1n2n2 + T3->Forwardn1n1n2n1n2)) +
		(NT1 -> (T0->Forwardn1n1n1n1n3 + T1->Forwardn1n1n3n2n3 + T2->Forwardn1n1n1n2n2 + T3->Forwardn1n1n2n3n1))

	maps = var0ton1var1ton1var2ton1->(var0->n1 + var1->n1 + var2->n1) +
		var0ton3var1ton2->(var0->n3 + var1->n2) +
		var1ton3var0ton2->(var1->n3 + var0->n2) +
		var0ton3var1ton3->(var0->n3 + var1->n3) +
		var0ton3var1ton3var2ton1->(var0->n3 + var1->n3 + var2->n1) +
		var0ton3var1ton2var2ton2->(var0->n3 + var1->n2 + var2->n2) +
		var1ton3var0ton2var2ton2->(var1->n3 + var0->n2 + var2->n2) +
		var2ton3var0ton3var1ton1->(var2->n3 + var0->n3 + var1->n1) +
		var2ton3var0ton2var1ton2->(var2->n3 + var0->n2 + var1->n2) +
		var2ton3var1ton3var0ton1->(var2->n3 + var1->n3 + var0->n1) +
		var0ton3var1ton2var2ton1->(var0->n3 + var1->n2 + var2->n1) +
		var1ton3var0ton2var2ton1->(var1->n3 + var0->n2 + var2->n1) +
		var0ton3var2ton2var1ton1->(var0->n3 + var2->n2 + var1->n1) +
		var0ton2var1ton2var2ton2->(var0->n2 + var1->n2 + var2->n2) +
		var1ton3var2ton2var0ton1->(var1->n3 + var2->n2 + var0->n1) +
		var2ton3var0ton2var1ton1->(var2->n3 + var0->n2 + var1->n1) +
		var2ton3var1ton2var0ton1->(var2->n3 + var1->n2 + var0->n1) +
		var0ton3var1ton1var2ton1->(var0->n3 + var1->n1 + var2->n1) +
		var0ton2var1ton2var2ton1->(var0->n2 + var1->n2 + var2->n1) +
		var1ton3var0ton1var2ton1->(var1->n3 + var0->n1 + var2->n1) +
		var0ton2->(var0->n2) +
		var0ton2var2ton2var1ton1->(var0->n2 + var2->n2 + var1->n1) +
		var1ton2var2ton2var0ton1->(var1->n2 + var2->n2 + var0->n1) +
		var2ton3var0ton1var1ton1->(var2->n3 + var0->n1 + var1->n1) +
		var0ton2var1ton1var2ton1->(var0->n2 + var1->n1 + var2->n1) +
		var1ton2var0ton1var2ton1->(var1->n2 + var0->n1 + var2->n1) +
		var0ton1->(var0->n1) +
		var2ton2var0ton1var1ton1->(var2->n2 + var0->n1 + var1->n1) +
		var2ton3var0ton3var1ton3->(var2->n3 + var0->n3 + var1->n3) +
		var0ton3->(var0->n3) +
		var0ton3var1ton3var2ton2->(var0->n3 + var1->n3 + var2->n2) +
		var2ton3var0ton3var1ton2->(var2->n3 + var0->n3 + var1->n2) +
		var2ton3var1ton3var0ton2->(var2->n3 + var1->n3 + var0->n2) +
		var0ton3var1ton1->(var0->n3 + var1->n1) +
		var0ton2var1ton2->(var0->n2 + var1->n2) +
		var1ton3var0ton1->(var1->n3 + var0->n1) +
		var0ton1var1ton1->(var0->n1 + var1->n1) +
		var0ton2var1ton1->(var0->n2 + var1->n1) +
		var1ton2var0ton1->(var1->n2 + var0->n1)

	baseName = Forwardn1n1n2n3n3->Forward +
		Forwardn1n1n2n3n2->Forward +
		Forwardn1n1n2n2n3->Forward +
		Forwardn2n1n2n2n2->Forward +
		Forwardn2n1n2n2n3->Forward +
		Forwardn2n1n2n2n1->Forward +
		Forwardn1n1n2n1n1->Forward +
		Forwardn1n1n2n3n1->Forward +
		Forwardn1n1n2n2n2->Forward +
		Forwardn1n1n2n2n1->Forward +
		Forwardn1n1n2n1n2->Forward +
		Forwardn1n1n3n1n2->Forward +
		Forwardn1n1n3n2n1->Forward +
		Forwardn1n1n3n1n1->Forward +
		Forwardn1n1n1n3n2->Forward +
		Forwardn1n1n1n2n3->Forward +
		Forwardn1n1n1n1n3->Forward +
		Forwardn1n1n1n3n1->Forward +
		Forwardn1n1n1n2n2->Forward +
		Forwardn1n1n1n1n2->Forward +
		Forwardn1n1n3n2n3->Forward +
		Forwardn1n1n1n2n1->Forward +
		Forwardn1n1n3n1n3->Forward +
		Forwardn1n1n1n1n1->Forward
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT166 extends PosTrace {} {}
one sig PT167 extends PosTrace {} {}
one sig PT168 extends PosTrace {} {}
one sig PT169 extends PosTrace {} {}
one sig PT170 extends PosTrace {} {}
one sig PT171 extends PosTrace {} {}
one sig PT172 extends PosTrace {} {}
one sig PT173 extends PosTrace {} {}
one sig PT174 extends PosTrace {} {}
one sig PT175 extends PosTrace {} {}
one sig PT176 extends PosTrace {} {}
one sig PT177 extends PosTrace {} {}
one sig PT178 extends PosTrace {} {}
one sig PT179 extends PosTrace {} {}
one sig PT180 extends PosTrace {} {}
one sig PT181 extends PosTrace {} {}
one sig PT182 extends PosTrace {} {}
one sig PT183 extends PosTrace {} {}
one sig PT184 extends PosTrace {} {}
one sig PT185 extends PosTrace {} {}
one sig PT186 extends PosTrace {} {}
one sig PT187 extends PosTrace {} {}
one sig PT188 extends PosTrace {} {}
one sig PT189 extends PosTrace {} {}
one sig PT190 extends PosTrace {} {}
one sig PT191 extends PosTrace {} {}
one sig PT192 extends PosTrace {} {}
