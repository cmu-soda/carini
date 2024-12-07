---------- MODULE check_bi -----------
CONSTANTS Server, Value, FinNat

VARIABLE messages
VARIABLE elections
VARIABLE allLogs
VARIABLE currentTerm
VARIABLE state
VARIABLE votedFor
VARIABLE log
VARIABLE commitIndex
VARIABLE votesResponded
VARIABLE votesGranted
VARIABLE voterLog
VARIABLE nextIndex
VARIABLE matchIndex

RaftOrig == INSTANCE raft_sms WITH
    Server <- Server,
    Value <- Value,
    messages <- messages,
    elections <- elections,
    allLogs <- allLogs,
    currentTerm <- currentTerm,
    state <- state,
    votedFor <- votedFor,
    log <- log,
    commitIndex <- commitIndex,
    votesResponded <- votesResponded,
    votesGranted <- votesGranted,
    voterLog <- voterLog,
    nextIndex <- nextIndex,
    matchIndex <- matchIndex
RaftTest == INSTANCE raft_sep WITH
    Server <- Server,
    Value <- Value,
    FinNat <- FinNat,
    messages <- messages,
    elections <- elections,
    allLogs <- allLogs,
    currentTerm <- currentTerm,
    state <- state,
    votedFor <- votedFor,
    log <- log,
    commitIndex <- commitIndex,
    votesResponded <- votesResponded,
    votesGranted <- votesGranted,
    voterLog <- voterLog,
    nextIndex <- nextIndex,
    matchIndex <- matchIndex

Spec == RaftTest!Spec
Safety == RaftOrig!Spec
=========
