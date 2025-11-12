--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot, Quorum

VARIABLES msgs2a, msgs2b

vars == <<msgs2a, msgs2b>>

CandSep ==
TRUE

None == "None"

TypeOK ==
/\ (msgs2a \in SUBSET((Ballot \X Value)))
/\ (msgs2b \in SUBSET((Acceptor \X Ballot \X Value)))

Init ==
/\ msgs2a = {}
/\ msgs2b = {}

Phase2a(b,v,a,Q) ==
/\ ~((\E m \in msgs2a : m[1] = b))
/\ msgs2a' = (msgs2a \cup {<<b,v>>})
/\ UNCHANGED <<msgs2b>>
/\ UNCHANGED<<>>
/\ CandSep'

Phase2b(a,b,v) ==
/\ (<<b,v>> \in msgs2a)
/\ msgs2b' = (msgs2b \cup {<<a,b,v>>})
/\ UNCHANGED <<msgs2a>>
/\ UNCHANGED<<>>
/\ CandSep'

Next ==
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : (\E Q \in Quorum : Phase2a(b,v,a,Q)))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)

ChosenAt(b,v) ==
\E Q \in Quorum :
\A a \in Q :
(<<a,b,v>> \in msgs2b)

chosen == { v \in Value : (\E b \in Ballot : ChosenAt(b,v)) }

Safety == (\A v,w \in chosen : v = w)
=============================================================================
