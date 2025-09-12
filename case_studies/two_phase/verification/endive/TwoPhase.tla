--------------------------- MODULE TwoPhase ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, tmState, onceSilentAbort, onceRcvAbort, tmPrepared, rmState, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare

vars == <<msgs, tmState, onceSilentAbort, onceRcvAbort, tmPrepared, rmState, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ onceSilentAbort = [ x0 \in RMs |-> FALSE]
/\ onceRcvAbort = [ x0 \in RMs |-> FALSE]
/\ onceRcvPrepare = [ x0 \in RMs |-> FALSE]
/\ onceRcvCommit = [ x0 \in RMs |-> FALSE]
/\ onceSndCommit = [ x0 \in RMs |-> FALSE]
/\ onceSndAbort = [ x0 \in RMs |-> FALSE]
/\ onceSndPrepare = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ onceSndPrepare' = [onceSndPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ onceRcvPrepare' = [onceRcvPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ onceSndCommit' = [onceSndCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndAbort, onceSndPrepare>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ onceRcvCommit' = [onceRcvCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort, onceSndPrepare>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ onceSndAbort' = [onceSndAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndPrepare>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ onceRcvAbort' = [onceRcvAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ onceSilentAbort' = [onceSilentAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>

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
/\ onceSilentAbort \in [RMs -> BOOLEAN]
/\ onceRcvAbort \in [RMs -> BOOLEAN]
/\ onceRcvPrepare \in [RMs -> BOOLEAN]
/\ onceRcvCommit \in [RMs -> BOOLEAN]
/\ onceSndCommit \in [RMs -> BOOLEAN]
/\ onceSndAbort \in [RMs -> BOOLEAN]
/\ onceSndPrepare \in [RMs -> BOOLEAN]

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))


\* inductive invariant generated for D0 by endive
D0_II ==
  /\ Consistent
  /\ \A rmi \in RMs : \A rmj \in RMs : (rmState[rmi] = "aborted") \/ (~(onceSilentAbort[rmi]))
  /\ \A rmi \in RMs : \A rmj \in RMs : (onceRcvCommit[rmj]) \/ (~(rmState[rmj] = "committed"))
  /\ \A rmi \in RMs : \A rmj \in RMs : (rmState[rmi] = "committed") \/ (~(onceRcvCommit[rmi]))
  /\ \A rmi \in RMs : \A rmj \in RMs : ~(onceSilentAbort[rmi]) \/ (~(onceSndPrepare[rmi]))
  /\ \A rmi \in RMs : \A rmj \in RMs : ~(onceSndPrepare[rmi]) \/ (~(rmState[rmi] = "working"))
  /\ \A rmi \in RMs : \A rmj \in RMs : (onceRcvAbort[rmi]) \/ (~(onceSndPrepare[rmi])) \/ (~(rmState[rmi] = "aborted"))


\* the assumption for D0 / the guarantee for D1
D1Guarantee ==
    /\ \A V \in RMs : (onceRcvCommit[V]) => (onceSndPrepare[V])
    /\ \A W \in RMs : \A V \in RMs : (onceRcvCommit[W]) => (onceSndPrepare[V])
    /\ \A V \in RMs : (onceRcvCommit[V]) => (\A W \in RMs : ~(onceRcvAbort[W]))

\* inductive invariant generated for D1 by endive
D1_II ==
  /\ D1Guarantee
  /\ \E rmi \in RMs : \A rmj \in RMs : ~([type |-> "Commit"] \in msgs) \/ (~(onceSndAbort[rmj]))
  /\ \E rmi \in RMs : \A rmj \in RMs : ~([type |-> "Abort"] \in msgs) \/ (~(onceSndCommit[rmj]))
  /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndAbort[rmi]) \/ (~(onceRcvAbort[rmj]))
  /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndCommit[rmi]) \/ (~(onceRcvCommit[rmj]))
  /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndPrepare[rmj]) \/ (~([type |-> "Commit"] \in msgs))
  /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndAbort[rmi]) \/ (~([type |-> "Abort"] \in msgs))
  /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndCommit[rmi]) \/ (~([type |-> "Commit"] \in msgs))
  /\ \E rmi \in RMs : \A rmj \in RMs : ([type |-> "Commit"] \in msgs) \/ (~(onceSndCommit[rmj]))
  /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndPrepare[rmj]) \/ (~(onceRcvPrepare[rmj]))
  /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndPrepare[rmj]) \/ (~([type |-> "Prepared", theRM |-> rmj] \in msgs))


\* the assumption for D1 / the guarantee for E1
E1Guarantee ==
    /\ \A V \in RMs : (onceSndCommit[V]) => (onceRcvPrepare[V])
    /\ \A V \in RMs : \A W \in RMs : (onceSndCommit[V]) => (onceRcvPrepare[W])
    /\ \A V \in RMs : (onceSndAbort[V]) => (~(onceSndCommit[V]))
    /\ \A V \in RMs : (onceSndCommit[V]) => (\A W \in RMs : ~(onceSndAbort[W]))

\* inductive invariant generated for E1 by endive
E1_II ==
  /\ E1Guarantee
  /\ \A rmi \in RMs : \A rmj \in RMs : ~(onceSndAbort[rmi]) \/ (~(tmState = "init"))
  /\ \A rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~(onceSndCommit[rmi]))
  /\ \A rmi \in RMs : \A rmj \in RMs : (onceRcvPrepare[rmi]) \/ (~(rmi \in tmPrepared))


IndInv ==
    /\ TypeOK
    /\ D0_II
    /\ D1_II
    /\ E1_II

IndInvSpec == IndInv /\ [][Next]_vars

=============================================================================
