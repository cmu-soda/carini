--------------------------- MODULE LogDebug ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Server, Quorums, FinNat
CONSTANTS n1,n2,n3

VARIABLES log, commitAtTermInd, leaderAtTermQuorum, committedThisTerm, leaderAtTermServ, leaderAtTerm, globalCurrentTerm, reqThisTerm, currentLeader, iStep

vars == <<log, commitAtTermInd, leaderAtTermQuorum, committedThisTerm, leaderAtTermServ, leaderAtTerm, globalCurrentTerm, reqThisTerm, currentLeader, iStep>>

Cex ==
/\ iStep = 0 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 1 =>
    /\ globalCurrentTerm = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 2 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 3 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<>> @@ n2 :> <<1>> @@ n3 :> <<>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 4 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<>> @@ n2 :> <<1, 1>> @@ n3 :> <<>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 5 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1>> @@ n2 :> <<1, 1>> @@ n3 :> <<>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 6 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1>> @@ n2 :> <<1, 1>> @@ n3 :> <<1>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 7 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1, 1>> @@ n2 :> <<1, 1>> @@ n3 :> <<1>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 8 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1, 1, 0>> @@ n2 :> <<1, 1>> @@ n3 :> <<1>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 9 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1, 1, 0>> @@ n2 :> <<1, 1>> @@ n3 :> <<1>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)

/\ iStep = 10 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1, 1, 0>> @@ n2 :> <<1, 1>> @@ n3 :> <<1>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> TRUE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> TRUE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> FALSE)

/\ iStep = 11 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1, 1, 0>> @@ n2 :> <<1, 1>> @@ n3 :> <<1, 2>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> TRUE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> TRUE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> TRUE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> FALSE)

/\ iStep = 12 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1, 1, 0>> @@ n2 :> <<1>> @@ n3 :> <<1, 2>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> TRUE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> TRUE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> TRUE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> FALSE)

/\ iStep = 13 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1, 1, 0>> @@ n2 :> <<1, 2>> @@ n3 :> <<1, 2>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> TRUE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> TRUE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> TRUE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> FALSE)

/\ iStep = 14 =>
    /\ globalCurrentTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)
    /\ currentLeader = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE) )
    /\ log = (n1 :> <<1, 1, 0>> @@ n2 :> <<1, 2>> @@ n3 :> <<1, 2>>)
    /\ leaderAtTermQuorum = ( 0 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      1 :>
          ( {n1, n2} :> TRUE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      2 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> TRUE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) @@
      3 :>
          ( {n1, n2} :> FALSE @@
            {n1, n3} :> FALSE @@
            {n2, n3} :> FALSE @@
            {n1, n2, n3} :> FALSE ) )
    /\ reqThisTerm = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> TRUE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ commitAtTermInd = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
      2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> FALSE) @@
      3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
    /\ committedThisTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)
    /\ leaderAtTermServ = ( 0 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
      1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
      2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> TRUE) @@
      3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
    /\ leaderAtTerm = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> FALSE)

Symmetry == Permutations(Server)
NextUnchanged == UNCHANGED vars

R2 ==
/\ \A t1 \in FinNat : \A t2 \in FinNat : (leaderAtTerm[t1]) => ((globalCurrentTerm[t2]) => (t1 <= t2))
/\ \A term \in FinNat : \A node \in Server : (reqThisTerm[term][node]) => (leaderAtTermServ[term][node])
/\ \A term \in FinNat : (committedThisTerm[term]) => (globalCurrentTerm[term])
/\ \A term \in FinNat : \E leaderQuorum \in Quorums : \A otherQuorum \in Quorums : (leaderAtTermQuorum[term][otherQuorum]) => (leaderQuorum = otherQuorum)
/\ \A term \in FinNat : \E leader \in Server : \A otherNode \in Server : leaderAtTermServ[term][otherNode] => otherNode = leader
/\ \A term \in FinNat : \A leader \in Server : reqThisTerm[term][leader] => currentLeader[leader][term]

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint ==
/\ (\A s \in Server : Len(log[s]) < 4)
\*/\ TLCGet("level") < 9

Empty(s) == Len(s) = 0

InLog(e,i) ==
\E x \in DOMAIN(log[i]) :
/\ x = e[1]
/\ log[i][x] = e[2]

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

CanRollback(i,j) ==
/\ LastTerm(log[i]) < LastTerm(log[j])
/\ ~(IsPrefix(log[i],log[j]))

CanVoteForOplog(i,j,term) ==
LET logOk == (LastTerm(log[j]) > LastTerm(log[i]) \/ (LastTerm(log[j]) = LastTerm(log[i]) /\ Len(log[j]) >= Len(log[i]))) IN
  /\ logOk

ClientRequest(i,curTerm) ==
/\ log' = [log EXCEPT![i] = Append(log[i],curTerm)]
/\ reqThisTerm' = [reqThisTerm EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED<<leaderAtTermQuorum, committedThisTerm, leaderAtTermServ, leaderAtTerm, globalCurrentTerm, currentLeader>>
/\ UNCHANGED<<commitAtTermInd>>
/\ R2'
/\ iStep' = iStep + 1
/\ Cex'

GetEntries(i,j) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ UNCHANGED<<leaderAtTermQuorum, committedThisTerm, leaderAtTermServ, leaderAtTerm, globalCurrentTerm, reqThisTerm, currentLeader>>
/\ UNCHANGED<<commitAtTermInd>>
/\ R2'
/\ iStep' = iStep + 1
/\ Cex'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<leaderAtTermQuorum, committedThisTerm, leaderAtTermServ, leaderAtTerm, globalCurrentTerm, reqThisTerm, currentLeader>>
/\ UNCHANGED<<commitAtTermInd>>
/\ R2'
/\ iStep' = iStep + 1
/\ Cex'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ leaderAtTermQuorum' = [leaderAtTermQuorum EXCEPT ![newTerm][voteQuorum] = TRUE]
/\ committedThisTerm' = [x0 \in FinNat |-> FALSE]
/\ leaderAtTermServ' = [leaderAtTermServ EXCEPT ![newTerm][i] = TRUE]
/\ leaderAtTerm' = [leaderAtTerm EXCEPT ![newTerm] = TRUE]
/\ globalCurrentTerm' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ reqThisTerm' = [x0 \in FinNat |-> [x1 \in Server |-> FALSE]]
/\ currentLeader' = [[currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]] EXCEPT ![i][newTerm] = TRUE]
/\ UNCHANGED <<log>>
/\ UNCHANGED<<commitAtTermInd>>
/\ R2'
/\ iStep' = iStep + 1
/\ Cex'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ committedThisTerm' = [committedThisTerm EXCEPT ![curTerm] = TRUE]
/\ commitAtTermInd' = [commitAtTermInd EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED <<log>>
/\ UNCHANGED<<leaderAtTermQuorum, leaderAtTermServ, leaderAtTerm, globalCurrentTerm, reqThisTerm, currentLeader>>
/\ R2'
/\ iStep' = iStep + 1
/\ Cex'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ leaderAtTermQuorum = [ x0 \in FinNat |-> [ x1 \in Quorums |-> FALSE]]
/\ committedThisTerm = [ x0 \in FinNat |-> FALSE]
/\ leaderAtTermServ = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ leaderAtTerm = [ x0 \in FinNat |-> FALSE]
/\ globalCurrentTerm = [ x0 \in FinNat |-> FALSE]
/\ commitAtTermInd = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ reqThisTerm = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ currentLeader = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ iStep = 0
/\ Cex

Next ==
\/ \E s \in Server : \E t \in FinNat : ClientRequest(s,t)
\/ \E s,t \in Server : GetEntries(s,t)
\/ \E s,t \in Server : RollbackEntries(s,t)
\/ \E s \in Server : \E Q \in Quorums : \E newTerm \in FinNat : BecomeLeader(s,Q,newTerm)
\/ \E s \in Server : \E Q \in Quorums : \E ind \in FinNat : \E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)

Spec == Init /\ [][Next]_vars

R1 == \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (commitAtTermInd[var0][var2]) => (var2 = var1)
IISafety == R1 /\ R2


TypeOK ==
/\ log         \in [Server -> Seq(FinNat)]
/\ commitAtTermInd     \in [FinNat -> [FinNat -> BOOLEAN]]
/\ leaderAtTermQuorum \in [FinNat -> [Quorums -> BOOLEAN]]
/\ committedThisTerm  \in [FinNat -> BOOLEAN]
/\ leaderAtTermServ  \in [FinNat -> [Server -> BOOLEAN]]
/\ leaderAtTerm  \in [FinNat -> BOOLEAN]
/\ globalCurrentTerm  \in [FinNat -> BOOLEAN]
/\ reqThisTerm \in [FinNat -> [Server -> BOOLEAN]]
/\ currentLeader \in [Server -> [FinNat -> BOOLEAN]]

FinSeq(S) == UNION {[1..n -> S] : n \in FinNat}

(*
TypeOKRand ==
/\ log         \in RandomSubset(7, [Server -> FinSeq(FinNat)])
/\ leaderAtTermQuorum \in RandomSubset(7, [FinNat -> [Quorums -> BOOLEAN]])
/\ committedThisTerm  \in RandomSubset(6, [FinNat -> BOOLEAN])
/\ leaderAtTermServ  \in RandomSubset(6, [FinNat -> [Server -> BOOLEAN]])
/\ leaderAtTerm  \in RandomSubset(6, [FinNat -> BOOLEAN])
/\ globalCurrentTerm  \in RandomSubset(6, [FinNat -> BOOLEAN])
/\ commitAtTermInd     \in RandomSubset(6, [FinNat -> [FinNat -> BOOLEAN]])
*)

TypeOKRand ==
/\ log         \in RandomSubset(9, [Server -> FinSeq(FinNat)])
/\ leaderAtTermQuorum \in RandomSubset(9, [FinNat -> [Quorums -> BOOLEAN]])
/\ committedThisTerm  \in RandomSubset(8, [FinNat -> BOOLEAN])
/\ leaderAtTermServ  \in RandomSubset(8, [FinNat -> [Server -> BOOLEAN]])
/\ leaderAtTerm  \in RandomSubset(8, [FinNat -> BOOLEAN])
/\ globalCurrentTerm  \in RandomSubset(8, [FinNat -> BOOLEAN])
/\ commitAtTermInd     \in RandomSubset(8, [FinNat -> [FinNat -> BOOLEAN]])

(*
TypeOKRand ==
/\ log         \in RandomSubset(13, [Server -> FinSeq(FinNat)])
/\ leaderAtTermQuorum \in RandomSubset(13, [FinNat -> [Quorums -> BOOLEAN]])
/\ committedThisTerm  \in RandomSubset(11, [FinNat -> BOOLEAN])
/\ leaderAtTermServ  \in RandomSubset(11, [FinNat -> [Server -> BOOLEAN]])
/\ leaderAtTerm  \in RandomSubset(11, [FinNat -> BOOLEAN])
/\ globalCurrentTerm  \in RandomSubset(11, [FinNat -> BOOLEAN])
/\ commitAtTermInd     \in RandomSubset(11, [FinNat -> [FinNat -> BOOLEAN]])
*)


\* time caffeinate -is python3 endive.py --spec benchmarks/C3 --seed 22 --ninvs 15000 --niters 10 --nrounds 10 --num_simulate_traces 100000 --simulate_depth 10 --tlc_workers 12 --opt_quant_minimize | tee out.log
IndInv ==
    /\ TypeOK
    /\ R1
    /\ R2

IndInvRand == TypeOKRand /\ IndInv

IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
