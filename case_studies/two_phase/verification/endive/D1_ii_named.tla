--------------------------- MODULE D1_ii_named ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC, Randomization

CONSTANTS RMs

VARIABLES msgs, onceSndCommit, onceRcvPrepare, onceSndAbort, onceRcvAbort, neverSndPrepare, neverRcvCommit

vars == <<msgs, onceSndCommit, onceRcvPrepare, onceSndAbort, onceRcvAbort, neverSndPrepare, neverRcvCommit>>

NextUnchanged == UNCHANGED vars
Symmetry == Permutations(RMs)

CandSep ==
/\ \A var0 \in RMs : (\E var1 \in RMs : onceSndCommit[var1]) => (onceRcvPrepare[var0])
/\ \A var0 \in RMs : (onceSndAbort[var0]) => (\A var1 \in RMs : ~onceSndCommit[var1])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ onceSndCommit = [ x0 \in RMs |-> FALSE]
/\ onceRcvPrepare = [ x0 \in RMs |-> FALSE]
/\ onceSndAbort = [ x0 \in RMs |-> FALSE]
/\ onceRcvAbort = [ x0 \in RMs |-> FALSE]
/\ neverSndPrepare = [ x0 \in RMs |-> TRUE]
/\ neverRcvCommit = [ x0 \in RMs |-> TRUE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED<<onceSndCommit, onceRcvPrepare, onceSndAbort>>
/\ CandSep'
/\ neverSndPrepare' = [neverSndPrepare EXCEPT![rm] = FALSE]
/\ UNCHANGED<<onceRcvAbort, neverRcvCommit>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ onceRcvPrepare' = [onceRcvPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndCommit, onceSndAbort>>
/\ CandSep'
/\ UNCHANGED<<onceRcvAbort, neverSndPrepare, neverRcvCommit>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ onceSndCommit' = [onceSndCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvPrepare, onceSndAbort>>
/\ CandSep'
/\ UNCHANGED<<onceRcvAbort, neverSndPrepare, neverRcvCommit>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<onceSndCommit, onceRcvPrepare, onceSndAbort>>
/\ CandSep'
/\ neverRcvCommit' = [neverRcvCommit EXCEPT![rm] = FALSE]
/\ UNCHANGED<<onceRcvAbort, neverSndPrepare>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ onceSndAbort' = [onceSndAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndCommit, onceRcvPrepare>>
/\ CandSep'
/\ UNCHANGED<<onceRcvAbort, neverSndPrepare, neverRcvCommit>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<onceSndCommit, onceRcvPrepare, onceSndAbort>>
/\ CandSep'
/\ onceRcvAbort' = [onceRcvAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<neverSndPrepare, neverRcvCommit>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ msgs \in SUBSET(Message)
/\ onceSndCommit  \in [RMs -> BOOLEAN]
/\ onceRcvPrepare  \in [RMs -> BOOLEAN]
/\ onceSndAbort \in [RMs -> BOOLEAN]
/\ onceRcvAbort  \in [RMs -> BOOLEAN]
/\ neverSndPrepare  \in [RMs -> BOOLEAN]
/\ neverRcvCommit  \in [RMs -> BOOLEAN]

Safety ==
/\ (\E var0 \in RMs : neverSndPrepare[var0]) => (\A var0 \in RMs : neverRcvCommit[var0])
/\ (\E var0 \in RMs : onceRcvAbort[var0]) => (\A var0 \in RMs : neverRcvCommit[var0])

IndInv ==
    /\ TypeOK
    /\ Safety
    /\ \A rmi \in RMs : \A rmj \in RMs : onceRcvAbort[rmi] => ~([type |-> "Commit"] \in msgs)
    /\ \A rmi \in RMs : \A rmj \in RMs : neverSndPrepare[rmi] => ~(onceRcvPrepare[rmi])
    /\ \A rmi \in RMs : \A rmj \in RMs : ([type |-> "Abort"] \in msgs) => neverRcvCommit[rmj]
    /\ \A rmi \in RMs : \A rmj \in RMs : ([type |-> "Commit"] \in msgs) => onceRcvPrepare[rmi]
    /\ \A rmi \in RMs : \A rmj \in RMs : onceSndCommit[rmi] => ([type |-> "Commit"] \in msgs)
    /\ \A rmi \in RMs : \A rmj \in RMs : onceSndAbort[rmi] => ([type |-> "Abort"] \in msgs)
    /\ \A rmi \in RMs : \A rmj \in RMs : ~([type |-> "Abort"] \in msgs) \/ ~([type |-> "Commit"] \in msgs)
    /\ \A rmi \in RMs : \A rmj \in RMs : ~([type |-> "Commit"] \in msgs) => neverRcvCommit[rmi]
    \* manual invariants
    /\ \A rm1 \in RMs : \E rm2 \in RMs : onceRcvAbort[rm1] => onceSndAbort[rm2]
    /\ \A rm1 \in RMs : \E rm2 \in RMs : ~neverRcvCommit[rm1] => onceSndCommit[rm2]
    /\ \E rm \in RMs : ([type |-> "Commit"] \in msgs) => onceSndCommit[rm]
    /\ \E rm \in RMs : ([type |-> "Abort"] \in msgs) => onceSndAbort[rm]
    /\ \A rm \in RMs : ([type |-> "Prepared", theRM |-> rm] \in msgs) => ~neverSndPrepare[rm]
    /\ \A rm \in RMs : ~neverSndPrepare[rm] => ([type |-> "Prepared", theRM |-> rm] \in msgs)

IISpec == IndInv /\ [][Next]_vars

=============================================================================
