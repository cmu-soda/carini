--------------------------- MODULE D0_ii ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS RMs

VARIABLES
    Fluent5, \* historically(~RcvAbort)
    Fluent4, \* once(RcvCommit)
    rmState,
    Fluent3, \* once(SndPrepare \/ RcvCommit)
    Fluent2  \* once(RcvCommit)

vars == <<Fluent5, Fluent4, rmState, Fluent3, Fluent2>>

NextUnchanged == UNCHANGED vars
Symmetry == Permutations(RMs)

CandSep ==
/\ \A var0 \in RMs : (Fluent2[var0]) => (\A var1 \in RMs : Fluent3[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent4[var0]) => (Fluent5[var1])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> TRUE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ Fluent3' = [Fluent3 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent5, Fluent4>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ Fluent3' = [Fluent3 EXCEPT![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent5>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ Fluent5' = [Fluent5 EXCEPT![rm] = FALSE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent4>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent5, Fluent4>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ Fluent3 \in [RMs -> BOOLEAN]
/\ Fluent2 \in [RMs -> BOOLEAN]
/\ Fluent5 \in [RMs -> BOOLEAN]
/\ Fluent4 \in [RMs -> BOOLEAN]

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

\* time python3 endive.py --spec benchmarks/D0 --seed 25 --ninvs 15000 --niters 3 --nrounds 4 --num_simulate_traces 50000 --simulate_depth 6 --tlc_workers 6
\* time: 14.606 seconds
IndInv ==
    /\ TypeOK
    /\ Consistent
    /\ \A rmi \in RMs : \A rmj \in RMs : (rmState[rmi] = "committed") \/ (~(Fluent2[rmi]))
    /\ \A rmi \in RMs : \A rmj \in RMs : (Fluent4[rmi]) \/ (~(rmState[rmi] = "committed"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (Fluent2[rmi]) \/ (~(Fluent4[rmi]))
    /\ \A rmi \in RMs : \A rmj \in RMs : ~(Fluent3[rmi]) \/ (~(rmState[rmi] = "working"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (Fluent3[rmj]) \/ (~(rmState[rmj] = "prepared"))
    /\ \A rmi \in RMs : \A rmj \in RMs : ~(Fluent3[rmi]) \/ (~(Fluent5[rmi]) \/ (~(rmState[rmi] = "aborted")))

IISpec == IndInv /\ [][Next]_vars

=============================================================================
