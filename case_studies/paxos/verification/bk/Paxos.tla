-------------------------------- MODULE Paxos -------------------------------
EXTENDS Integers, FiniteSets, TLC, Randomization

CONSTANT Value, Acceptor

Quorum == {i \in SUBSET(Acceptor) : Cardinality(i) * 2 > Cardinality(Acceptor)}

\* ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                        \*    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
      
Ballot == Nat

None == CHOOSE v : v \notin Value

Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]


Message1a ==      [type : {"1a"}, bal : Ballot]
Message1b ==      [type : {"1b"}, acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value \cup {None}]
Message2a ==      [type : {"2a"}, bal : Ballot, val : Value]
Message2b ==      [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

-----------------------------------------------------------------------------
VARIABLE maxBal, 
         maxVBal, \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
         maxVal,    \* ballot number cast by a; it equals <<-1, None>> if
                    \* a has not cast any vote.
         msgs1a,     \* The set of all messages that have been sent.
         msgs1b,     \* The set of all messages that have been sent.
         msgs2a,     \* The set of all messages that have been sent.
         msgs2b,     \* The set of all messages that have been sent.
         chosen

vars == <<maxBal, maxVBal, maxVal, msgs1a, msgs1b, msgs2a, msgs2b, chosen>>

TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal \in [Acceptor -> Value \cup {None}]
          /\ msgs1a \in SUBSET Message1a
          /\ msgs1b \in SUBSET Message1b
          /\ msgs2a \in SUBSET Message2a
          /\ msgs2b \in SUBSET Message2b
          /\ chosen \in SUBSET Value


Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVal = [a \in Acceptor |-> None]
    /\ msgs1a = {}
    /\ msgs1b = {}
    /\ msgs2a = {}
    /\ msgs2b = {}
    /\ chosen = {}

Send(m, ms) == ms' = ms \cup {m}

\* Helper predicates for checking presence of message types.
msg1a(a,b) == \E m \in msgs1a : m.type= "1b" /\ m.bal = a
msg1b(a,b,mb,v) == \E m \in msgs1b : m.type= "1b" /\ m.acc = a /\ m.bal = b /\ m.mbal = mb /\ m.mval = v
msg2a(b,v) == \E m \in msgs2a : m.type= "2a" /\ m.bal = b /\ m.val = v
msg2b(a,b,v) == \E m \in msgs2b : m.type= "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

Phase1a(b) == 
    /\ msgs1a' = msgs1a \cup {[type |-> "1a", bal |-> b]}
    /\ UNCHANGED <<maxBal, maxVBal,maxVal,msgs1b,msgs2a,msgs2b,chosen>>
                 
Phase1b(a) == 
    \E m \in msgs1a : 
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ msgs1b' = msgs1b \cup {[type |-> "1b", acc |-> a, bal |-> m.bal, mbal |-> maxVBal[a], mval |-> maxVal[a]]}
        /\ UNCHANGED <<maxVBal, maxVal,msgs1a,msgs2a,msgs2b,chosen>>

Q1b(Q, b) ==
    {m \in msgs1b : /\ m.type = "1b"
                    /\ m.acc \in Q
                    /\ m.bal = b}

Q1bv(Q, b) == {m \in Q1b(Q,b) : m.mbal \geq 0}
    
Phase2a(b, v) ==
  /\ ~ \E m \in msgs2a : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorum :
        /\ \A a \in Q : \E m \in Q1b(Q,b) : m.acc = a 
        /\ \/ Q1bv(Q, b) = {}
           \/ \E m \in Q1bv(Q, b) : 
                /\ m.mval = v
                /\ \A mm \in Q1bv(Q, b) : m.mbal \geq mm.mbal 
  /\ msgs2a' = msgs2a \cup {[type |-> "2a", bal |-> b, val |-> v]}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal,msgs1a,msgs1b,msgs2b,chosen>>
  
Phase2b(a) == 
    \E m \in msgs2a : 
        /\ m.type = "2a"
        /\ m.bal \geq maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal] 
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal] 
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ msgs2b' = msgs2b \cup {[type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val]} 
        /\ UNCHANGED <<msgs1a,msgs1b,msgs2a,chosen>>


votes == [a \in Acceptor |->  
           {<<m.bal, m.val>> : m \in {mm \in msgs2b: /\ mm.type = "2b"
                                                     /\ mm.acc = a }}]
               
VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

\* chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Learn(val) == 
    /\ val \in {v \in Value : \E b \in Ballot : ChosenAt(b, v)}
    /\ chosen' = chosen \cup {val}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs1a, msgs1b, msgs2a, msgs2b>>

Next == 
    \/ \E b \in Ballot : Phase1a(b)
    \/ \E b \in Ballot : \E v \in Value : Phase2a(b, v)
    \/ \E a \in Acceptor : Phase1b(a) 
    \/ \E a \in Acceptor : Phase2b(a)
    \/ \E v \in Value : Learn(v)

Spec == Init /\ [][Next]_vars

Safety == Cardinality(chosen) <= 1

============================================================================
