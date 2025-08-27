@!@!@STARTMSG 1000:0 @!@!@
Will generate a SpecTE file pair if error states are encountered.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 2262:0 @!@!@
TLC2 Version 2.19 of 08 August 2024 (rev: 5a47802)
@!@!@ENDMSG 2262 @!@!@
@!@!@STARTMSG 2401:3 @!@!@
Please run the Java VM which executes TLC with a throughput optimized garbage collector by passing the "-XX:+UseParallelGC" property.
@!@!@ENDMSG 2401 @!@!@
@!@!@STARTMSG 2187:0 @!@!@
Running breadth-first search Model-Checking with fp 80 and seed 7638874455482940152 with 8 workers on 10 cores with 8192MB heap and 64MB offheap memory [pid: 30446] (Mac OS X 14.2.1 aarch64, Oracle Corporation 18.0.2.1 x86_64, MSBDiskFPSet, DiskStateQueue).
@!@!@ENDMSG 2187 @!@!@
@!@!@STARTMSG 2220:0 @!@!@
Starting SANY...
@!@!@ENDMSG 2220 @!@!@
Parsing file /Users/idardik/Documents/CMU/compositional_ii/tla-sym-assump-synth/examples/client_server_db_ae/cust_decomp2/D0.tla
Parsing file /private/var/folders/dl/hzl20bt96699x9wpnq61qdmc0000gq/T/Naturals.tla
Parsing file /private/var/folders/dl/hzl20bt96699x9wpnq61qdmc0000gq/T/Sequences.tla
Parsing file /private/var/folders/dl/hzl20bt96699x9wpnq61qdmc0000gq/T/FiniteSets.tla
Parsing file /private/var/folders/dl/hzl20bt96699x9wpnq61qdmc0000gq/T/TLC.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module D0
@!@!@STARTMSG 2219:0 @!@!@
SANY finished.
@!@!@ENDMSG 2219 @!@!@
@!@!@STARTMSG 2185:0 @!@!@
Starting... (2024-11-22 09:54:56)
@!@!@ENDMSG 2185 @!@!@
@!@!@STARTMSG 2189:0 @!@!@
Computing initial states...
@!@!@ENDMSG 2189 @!@!@
@!@!@STARTMSG 2269:0 @!@!@
Computed 2 initial states...
@!@!@ENDMSG 2269 @!@!@
@!@!@STARTMSG 2269:0 @!@!@
Computed 4 initial states...
@!@!@ENDMSG 2269 @!@!@
@!@!@STARTMSG 2269:0 @!@!@
Computed 8 initial states...
@!@!@ENDMSG 2269 @!@!@
@!@!@STARTMSG 2269:0 @!@!@
Computed 16 initial states...
@!@!@ENDMSG 2269 @!@!@
@!@!@STARTMSG 2269:0 @!@!@
Computed 32 initial states...
@!@!@ENDMSG 2269 @!@!@
@!@!@STARTMSG 2269:0 @!@!@
Computed 64 initial states...
@!@!@ENDMSG 2269 @!@!@
@!@!@STARTMSG 2269:0 @!@!@
Computed 128 initial states...
@!@!@ENDMSG 2269 @!@!@
@!@!@STARTMSG 2269:0 @!@!@
Computed 256 initial states...
@!@!@ENDMSG 2269 @!@!@
@!@!@STARTMSG 2190:0 @!@!@
Finished computing initial states: 512 distinct states generated at 2024-11-22 09:54:57.
@!@!@ENDMSG 2190 @!@!@
@!@!@STARTMSG 2110:1 @!@!@
Invariant Safety is violated.
@!@!@ENDMSG 2110 @!@!@
@!@!@STARTMSG 2121:1 @!@!@
The behavior up to this point is:
@!@!@ENDMSG 2121 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
1: <Initial predicate>
/\ request_sent = {}
/\ match = {<<req2, resp2>>}
/\ response_received = {}
/\ response_sent = {}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
2: <ServerProcessDbResponse line 30, col 1 to line 31, col 53 of module D0>
/\ request_sent = {}
/\ match = {<<req2, resp2>>}
/\ response_received = {}
/\ response_sent = {<<n2, resp1>>}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
3: <ReceiveResponse line 34, col 1 to line 36, col 49 of module D0>
/\ request_sent = {}
/\ match = {<<req2, resp2>>}
/\ response_received = {<<n2, resp1>>}
/\ response_sent = {<<n2, resp1>>}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2200:0 @!@!@
Progress(3) at 2024-11-22 09:54:57: 21,243 states generated (3,550,362 s/min), 10,676 distinct states found (1,784,289 ds/min), 10,081 states left on queue.
@!@!@ENDMSG 2200 @!@!@
@!@!@STARTMSG 2199:0 @!@!@
21243 states generated, 10676 distinct states found, 10081 states left on queue.
@!@!@ENDMSG 2199 @!@!@
@!@!@STARTMSG 2194:0 @!@!@
The depth of the complete state graph search is 3.
@!@!@ENDMSG 2194 @!@!@
@!@!@STARTMSG 2268:0 @!@!@
The average outdegree of the complete state graph is 17 (minimum is 9, the maximum 18 and the 95th percentile is 18).
@!@!@ENDMSG 2268 @!@!@
@!@!@STARTMSG 1000:0 @!@!@
The model check run produced error-states - we will generate the SpecTE files now.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 1000:0 @!@!@
The file /Users/idardik/Documents/CMU/compositional_ii/tla-sym-assump-synth/examples/client_server_db_ae/cust_decomp2/SpecTE.tla has been created.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 1000:0 @!@!@
The file /Users/idardik/Documents/CMU/compositional_ii/tla-sym-assump-synth/examples/client_server_db_ae/cust_decomp2/SpecTE.cfg has been created.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 2186:0 @!@!@
Finished in 375ms at (2024-11-22 09:54:57)
@!@!@ENDMSG 2186 @!@!@
--------------------------- MODULE SpecTE ----
EXTENDS Sequences, Toolbox, TLC, Naturals, FiniteSets

\* 
\*  SpecTE follows
\* 


CONSTANTS Node, Request, Response, DbRequestId

VARIABLES request_sent, response_sent, match, response_received

Symmetry == Permutations(Node) \cup Permutations(Request) \cup Permutations(Response) \cup Permutations(DbRequestId)

vars == <<match,request_sent,response_sent,response_received>>

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received>>

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>

Next ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))
/\ request_sent = {}
/\ response_sent = {}
/\ response_received = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))

CONSTANTS req3, req2, n1, n2, resp2, n3, resp3, req1, id2, resp1, id1

\* TRACE Sub-Action definition 0
Spec_sa_0 ==
    (
        /\ request_sent = (
                {}
            )
        /\ match = (
                {<<req2, resp2>>}
            )
        /\ response_received = (
                {}
            )
        /\ response_sent = (
                {}
            )
        /\ request_sent' = (
                {}
            )
        /\ match' = (
                {<<req2, resp2>>}
            )
        /\ response_received' = (
                {}
            )
        /\ response_sent' = (
                {<<n2, resp1>>}
            )
    )

\* TRACE Action Constraint definition traceExploreActionConstraint
_SpecTEActionConstraint ==
<<
Spec_sa_0
>>[TLCGet("level")]
----

def_ov_17322872972282000 == 
<<
([request_sent |-> {},match |-> {<<req2, resp2>>},response_received |-> {},response_sent |-> {}]),
([request_sent |-> {},match |-> {<<req2, resp2>>},response_received |-> {},response_sent |-> {<<n2, resp1>>}])
>>
----


\* VARIABLE TraceExp

\* TRACE INIT definition traceExploreInit
_SpecTEInit ==
    /\ request_sent = (
            {}
        )
    /\ match = (
            {<<req2, resp2>>}
        )
    /\ response_received = (
            {}
        )
    /\ response_sent = (
            {}
        )
\*     /\ TraceExp = TRUE

----

\* TRACE NEXT definition traceExploreNext
_SpecTENext ==
/\  \/ Spec_sa_0
\* /\ TraceExp' = TraceExp



=============================================================================
