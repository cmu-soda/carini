--------------------------- MODULE TwoPhase_ii ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC, Randomization

CONSTANTS RMs

VARIABLES msgs, tmState, tmPrepared, rmState, Fluent9, Fluent8, Fluent10, Fluent5, Fluent3, Fluent2

vars == <<msgs, tmState, tmPrepared, rmState, Fluent9, Fluent8, Fluent10, Fluent5, Fluent3, Fluent2>>

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent3 = [ x0 \in RMs |-> TRUE]
/\ Fluent2 = [ x0 \in RMs |-> TRUE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ UNCHANGED<<Fluent9, Fluent8, Fluent10>>
/\ Fluent3' = [Fluent3 EXCEPT![rm] = FALSE]
/\ UNCHANGED<<Fluent5, Fluent2>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ Fluent8' = [Fluent8 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent10>>
/\ UNCHANGED<<Fluent5, Fluent3, Fluent2>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent9' = [Fluent9 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent8, Fluent10>>
/\ UNCHANGED<<Fluent5, Fluent3, Fluent2>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ UNCHANGED<<Fluent9, Fluent8, Fluent10>>
/\ Fluent2' = [Fluent2 EXCEPT![rm] = FALSE]
/\ UNCHANGED<<Fluent5, Fluent3>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent10' = [Fluent10 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent8>>
/\ UNCHANGED<<Fluent5, Fluent3, Fluent2>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ UNCHANGED<<Fluent9, Fluent8, Fluent10>>
/\ Fluent5' = [Fluent5 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2>>

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED<<msgs, tmState, tmPrepared>>
/\ UNCHANGED<<Fluent3, Fluent2, Fluent5>>
/\ UNCHANGED<<Fluent10, Fluent8, Fluent9>>

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (msgs \in SUBSET(Message))
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent9  \in [RMs -> BOOLEAN]
/\ Fluent8  \in [RMs -> BOOLEAN]
/\ Fluent10 \in [RMs -> BOOLEAN]
/\ Fluent5  \in [RMs -> BOOLEAN]
/\ Fluent3  \in [RMs -> BOOLEAN]
/\ Fluent2  \in [RMs -> BOOLEAN]

TypeOKRandom ==
/\ (msgs \in SUBSET(Message))
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent9  \in RandomSubset(3, [RMs -> BOOLEAN])
/\ Fluent8  \in RandomSubset(3, [RMs -> BOOLEAN])
/\ Fluent10 \in RandomSubset(3, [RMs -> BOOLEAN])
/\ Fluent5  \in RandomSubset(3, [RMs -> BOOLEAN])
/\ Fluent3  \in RandomSubset(3, [RMs -> BOOLEAN])
/\ Fluent2  \in RandomSubset(3, [RMs -> BOOLEAN])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

D1_Safety ==
/\ (\E var0 \in RMs : Fluent3[var0]) => (\A var0 \in RMs : Fluent2[var0])
/\ (\E var0 \in RMs : Fluent5[var0]) => (\A var0 \in RMs : Fluent2[var0])

E1_Safety ==
/\ \A var0 \in RMs : (\E var1 \in RMs : Fluent9[var1]) => (Fluent8[var0])
/\ \A var0 \in RMs : (Fluent10[var0]) => (\A var1 \in RMs : ~Fluent9[var1])

IndInv ==
    \* D0
    /\ Consistent
    /\ \A rmi \in RMs : \A rmj \in RMs : ~(Fluent2[rmi]) \/ (~(rmState[rmi] = "committed"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (Fluent2[rmj]) \/ ((rmState[rmj] = "committed"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (Fluent3[rmi]) \/ (~(rmState[rmi] = "working"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (Fluent3[rmj]) \/ (~(rmState[rmj] = "aborted")) \/ ((Fluent5[rmj]))

    \* D1
    /\ D1_Safety
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : ~(Fluent5[rmi]) \/ (~([type |-> "Commit"] \in msgs))
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : ([type |-> "Prepared", theRM |-> rmi] \in msgs) \/ (~(Fluent8[rmi]))
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : (Fluent9[rmk]) \/ (~([type |-> "Commit"] \in msgs))
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : ~(Fluent3[rmi]) \/ (~([type |-> "Prepared", theRM |-> rmi] \in msgs))
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : (Fluent2[rmi]) \/ (([type |-> "Commit"] \in msgs))
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : (Fluent10[rmk]) \/ (~([type |-> "Abort"] \in msgs))
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : (Fluent10[rmk]) \/ (~(Fluent5[rmi]))

    \* E1
    /\ E1_Safety
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : ~(Fluent10[rmi]) \/ (~(tmState = "init"))
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : (tmState = "committed") \/ (~(Fluent9[rmi]))
    /\ \A rmi \in RMs : \A rmj \in RMs : \E rmk \in RMs : (Fluent8[rmi]) \/ (~(tmPrepared = tmPrepared \cup {rmi}))

IISpec == TypeOKRandom/\ IndInv /\ [][Next]_vars

=============================================================================
