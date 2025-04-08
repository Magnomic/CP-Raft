 --------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the CP-Raft consensus algorithm.
\*
\* Copyright 2024 Haiwen Du.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* Server states.
CONSTANTS Follower, PreCandidate, Candidate, Leader, FullLeader

\* A reserved value.
CONSTANTS Nil

\* A reserved value.
CONSTANTS Conf

\* A reserved value.
CONSTANTS Gap

\* A reserved value.
CONSTANTS ConfirmedGap

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          RequestPreVoteRequest, RequestPreVoteResponse,
          RequestFullVoteRequest, RequestFullVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse
          
\* Maximum number of client requests
CONSTANTS MaxClientRequests



----
\* Global variables
\* TODO(irfansharif): Allow transition from follower to candidate directly?
\* Semi-randomly i.e.


\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
VARIABLE allLogs

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, PreCandidate, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* The set of requests that can go into the log
VARIABLE clientRequests

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
\* The index that gets committed
VARIABLE committedLog
\* Does the commited Index decrease
VARIABLE committedLogDecrease
\* @ start point of o3 entries
VARIABLE o3StartIndex
\* @ Committed o3 entries
VARIABLE o3CommitIndexes
logVars == <<log, o3StartIndex, o3CommitIndexes, commitIndex, clientRequests, committedLog, committedLogDecrease>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesSent
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
\* @ o3 entries that missing in prevote (Only record the start point)
VARIABLE o3MissingLog
candidateVars == <<o3MissingLog, votesSent, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
\* @ o3MatchIndex is the records the replicating status of entries after matchIndex (which is the last sequential commit index)
VARIABLE o3MatchIndexes
leaderVars == <<nextIndex, matchIndex, o3MatchIndexes, elections>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* @ Get term of specific index
GetTerm(xlog, idx) == IF Len(xlog) = 0 \/ idx = 0 THEN 0 ELSE xlog[idx].term
 

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
\*        [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
        msgs
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE
        msgs
        
ValidMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] > 0 }
    
InvalidMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] = 0 }
    
SingleMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] = 1 } 

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitHistoryVars == /\ elections = {}
                   /\ allLogs   = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
                   
                   
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
                  
                  
                  
InitCandidateVars == /\ votesSent = [i \in Server |-> FALSE ]
                     /\ votesGranted = [i \in Server |-> {}]
                     \* @ Records the entries of start point that nodes missing.
                     /\ o3MissingLog = [i \in Server |-> [j \in Server |-> 1]]
                     
                     
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
                  
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
                  /\ o3MatchIndexes = [i \in Server |-> [j \in Server |-> {}]]
                  
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
               /\ clientRequests = 1
               /\ committedLog = << >>
               /\ committedLogDecrease = FALSE
               \* @ every node saves a o3 start index.
               /\ o3StartIndex = [i \in Server |-> 0]
               /\ o3CommitIndexes = [i \in Server |-> [j \in Server |-> {}]]
               
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.

\* @ No changes needed when restart
Restart(i) ==
           /\ state'          = [state EXCEPT ![i] = Follower]
           /\ votesSent'      = [votesSent EXCEPT ![i] = FALSE ]
           /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
           /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
           /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
           /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
           \* @ reset the o3 log matching stats.
           /\ o3MatchIndexes'   = [o3MatchIndexes EXCEPT ![i] = [j \in Server |-> {}]]
           /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
           \* @ reset the o3 log commit stats.
           /\ o3CommitIndexes'   = [o3CommitIndexes EXCEPT ![i] = [j \in Server |-> {}]]
           \* @ reset the missing log entries.
           /\ o3MissingLog'   = [o3MissingLog EXCEPT ![i] = [j \in Server |-> 1]]
           \* @ added o3StartIndex here but not changed. o3StartIndex can be recoverd from log entries.
           /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections, clientRequests, committedLog, committedLogDecrease, o3StartIndex>>

\* Server i times out and enters PreCandidate phase.
Timeout(i) == 
    /\ state[i] \in {Follower} \*, PreCandidate, Candidate
    /\ state' = [state EXCEPT ![i] = PreCandidate]
    /\ UNCHANGED currentTerm
    \* Most implementations would probably just set the local vote
    \* atomically, but messaging localhost for it is weaker.
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ votesSent' = [votesSent EXCEPT ![i] = FALSE ]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    \* @ reset the missing log entries.
    /\ o3MissingLog'   = [o3MissingLog EXCEPT ![i] = [j \in Server |-> 1]]
    /\ UNCHANGED <<messages, leaderVars, logVars>>

CheckO3StartPoint(i, thisLog) == 
    IF Len(thisLog) /= 0 THEN
        LET newMatchIndexes == {index \in Max({o3StartIndex[i], 1})..Len(thisLog) 
                                                                      : thisLog[index].value /= Gap }
            \* @ Find gaps
            newO3StartIndexCandidate == {index \in newMatchIndexes 
                                              : index + 1 \notin newMatchIndexes}
           
            \* @ Find min gap start point as new o3 start index
            newO3StartIndex ==  IF Cardinality(newO3StartIndexCandidate) > 0 THEN 
                                    CHOOSE index \in newO3StartIndexCandidate: 
                                           \A index2 \in newO3StartIndexCandidate: index2 >= index
                                ELSE Len(thisLog)
            \* @ Filter the o3 part of match indexes
            newO3MatchIndex == IF newO3StartIndex = Len(thisLog) THEN {}
                               ELSE {index \in newMatchIndexes: index > newO3StartIndex}
        IN 
            << newO3StartIndex, newO3MatchIndex >>
    ELSE << 0, {} >>
    
\* PreCandidate i sends j a RequestPreVote request.
\* @ Tell dest node my start point of o3 and the entries that I need to sync.
\* @ In prevote, node j needs to sync all the entries it has to i in target term, but not care about the previous term or the o3 entries before o3StartIndex.
RequestPreVote(i,j) ==
    /\ state[i] = PreCandidate
    \* @ Find all the empty entries and pack them.
    /\ LET newO3StartIndex == CheckO3StartPoint(i, log[i])[1]
           o3NeedSync == IF Len(log[i]) - newO3StartIndex > 0 
                         THEN 
                            \* find all indexes that server i miss
                            {index \in newO3StartIndex..Len(log[i]) : log[i][index].value = Gap}
                         ELSE
                            {}
       
       IN  /\ o3StartIndex' = [o3StartIndex EXCEPT ![i] = newO3StartIndex]
           /\ Send( [mtype         |-> RequestPreVoteRequest,
                     mterm         |-> currentTerm[i],
                     mlastLogTerm  |-> LastTerm(log[i]),
                     mlastLogIndex |-> Len(log[i]),
                     msource       |-> i,
                     mdest         |-> j,
                     \* @ send the o3 start index. (Although it can be calculated)
                     mo3StartIndex |-> newO3StartIndex,
                     \* @ send the term of o3 start index. (Although it can be calculated)
                     mo3StartTerm  |-> GetTerm(log[i], o3StartIndex[i]),
                     \* @ send all the indexs of empty entries (gaps). {2, 4, 5, 7, 8}
                     mo3NeedSync   |-> o3NeedSync
                     ])
    /\ UNCHANGED <<serverVars, votesGranted, voterLog, leaderVars, votesSent, o3MissingLog, log,
                   o3CommitIndexes, commitIndex, clientRequests, committedLog, committedLogDecrease>>

\* Candidate i sends j a RequestVote request.
\* @ Send the entries that other nodes need.
RequestVote(i,j) ==
    /\ state[i] = Candidate
    \* @ Find the start point of out of order entries. If no records (node j did not reply to i), i will send empty request to ask the start point 
    /\ LET o3ToSyncIndexes == o3MissingLog[i][j]
           \* @ if it has some entries to sync, add them to the request 
           o3ToSyncEntries == IF o3ToSyncIndexes /= 0 /\ o3ToSyncIndexes <= Len(log[i]) THEN log[i][o3ToSyncIndexes] ELSE Nil
           o3lastLogTerm == IF o3ToSyncIndexes /= 0 /\ o3ToSyncIndexes <= Len(log[i]) /\ o3ToSyncIndexes - 1 /= 0  
                                THEN log[i][o3ToSyncIndexes - 1].term ELSE 0
       IN  Send([mtype         |-> RequestVoteRequest,
                 mterm         |-> currentTerm[i],
                 mlastLogTerm  |-> LastTerm(log[i]),
                 mlastLogIndex |-> Len(log[i]),
                 mo3ToSyncIndexes |-> o3ToSyncIndexes,
                 mo3ToSyncEntries |-> o3ToSyncEntries,
                 mo3lastLogTerm   |-> o3lastLogTerm,
                 msource       |-> i,
                 mdest         |-> j])
    /\ UNCHANGED <<serverVars, votesGranted, voterLog, leaderVars, logVars, votesSent, o3MissingLog>>

RequestFullVote(i, j) == 
    /\ state[i] = Leader
    /\ LET toSyncLogIndex == Min({nextIndex[i][j], o3MissingLog[i][j]})
           prevLogIndex == toSyncLogIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), toSyncLogIndex})
           entries == SubSeq(log[i], toSyncLogIndex, lastEntry)
       IN /\ Send([mtype         |-> RequestFullVoteRequest,
                  mterm          |-> currentTerm[i],
                  mprevLogIndex  |-> prevLogIndex,
                  mprevLogTerm   |-> prevLogTerm,
                  mentries       |-> entries,
                  \* mlog is used as a history variable for the proof.
                  \* It would not exist in a real implementation.
                  mlog           |-> log[i],
                  mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                  msource        |-> i,
                  mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.

\* @ Parallel raft still append the sequence in order, but follower may receive and reply them in random sequence. 
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = FullLeader
    /\ LET notMatchIndexes == {y \in (matchIndex[i][j] + 1) .. Len(log[i]): y \notin o3MatchIndexes[i][j]} \cup {Len(log[i])}
           newNextIndex == IF nextIndex[i][j] > Len(log[i]) THEN
                              CHOOSE x \in notMatchIndexes : TRUE
                           ELSE
                              nextIndex[i][j]
           prevLogIndex == newNextIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), newNextIndex})
           entries == SubSeq(log[i], newNextIndex, lastEntry)
           o3Committed == IF currentTerm[i] = prevLogTerm
                          THEN o3MatchIndexes[i][j] \cap o3CommitIndexes[i]
                          ELSE {index \in 1 .. Len(log[i]): log[i][index].value /= ConfirmedGap /\ log[i][index].term = prevLogTerm}
       IN /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({newNextIndex + 1, nextIndex[i][j]})]
          /\ Send([mtype          |-> AppendEntriesRequest,
                  mterm          |-> currentTerm[i],
                  mprevLogIndex  |-> prevLogIndex,
                  mprevLogTerm   |-> prevLogTerm,
                  mentries       |-> entries,
                  mo3commitIndex |-> o3Committed,
                  \* mlog is used as a history variable for the proof.
                  \* It would not exist in a real implementation.
                  mlog           |-> log[i],
                  mcommitIndex   |-> Min({commitIndex[i], matchIndex[i][j]}),
                  msource        |-> i,
                  mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, matchIndex, o3MatchIndexes, elections, logVars>>


BecomeFullLeader(i) == 
    /\ state[i] = Leader
    \* apply configurations
    /\ LET confEntries == {index \in 1..Len(log[i]) : log[i][index].value = Conf}
           confirmedGaps == UNION {log[i][index2].conf: index2 \in confEntries}
           newLog == [index3 \in 1..Len(log[i]) |-> IF index3 \in confirmedGaps THEN [term  |-> log[i][index3].term, 
                                                                                      value |-> ConfirmedGap,
                                                                                      conf  |-> {}]
                                                                                ELSE log[i][index3]]
       IN  /\ commitIndex' = [commitIndex EXCEPT ![i] = Len(newLog)] 
           /\ o3CommitIndexes' = [o3CommitIndexes EXCEPT ![i] = {}] 
           /\ log' = [log EXCEPT ![i] = newLog]                                                                   
           /\ \/ Len(log[i]) = 0
              \/ /\ Len(log[i]) > 0
                 /\ log[i][Len(log[i])].value = Conf \* The configuration has been added
                 /\ log[i][Len(log[i])].term = currentTerm[i]
           /\ votesGranted[i] \in Quorum
           /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                                [j \in Server |-> Len(log[i]) + 1]] 
           /\ state'      = [state EXCEPT ![i] = FullLeader]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, matchIndex, o3MatchIndexes, elections,
                   o3StartIndex, clientRequests, committedLog, committedLogDecrease>>
    
\* Candidate i transitions to leader.

\* @ No need to change
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum 
    /\ LET lastTerm == LastTerm(log[i])
           gaps == {index \in 1..Len(log[i]) : log[i][index].value = Gap}
           entry == [term  |-> currentTerm[i],
                     value |-> Conf,
                     conf  |-> gaps]
           newLog == Append(log[i], entry)
       IN /\ log'        = [log EXCEPT ![i] = newLog]
          /\ state'      = [state EXCEPT ![i] = Leader]
          /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                               [j \in Server |-> Len(log[i]) + 1]] \* All nodes j must receive conf before i can provide service
          /\ o3MissingLog' = [nextIndex EXCEPT ![i] =
                               [j \in Server |-> Len(newLog) + 1]]
          /\ matchIndex' = [matchIndex EXCEPT ![i] =
                               [j \in Server |-> 0]]
          \* @ reset the o3 log matching stats.
          /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
          /\ o3MatchIndexes' = [o3MatchIndexes EXCEPT ![i] = [j \in Server |-> {}]]
          /\ elections'  = elections \cup
                               {[eterm     |-> currentTerm[i],
                                 eleader   |-> i,
                                 elog      |-> log[i],
                                 evotes    |-> votesGranted[i],
                                 evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, currentTerm, votedFor, votesSent, voterLog, o3StartIndex, o3CommitIndexes, commitIndex, clientRequests, committedLog, committedLogDecrease>>

\* PreCandidate i transitions to Candidate.

\* @ No need to change
BecomeCandidate(i) ==
              /\ state[i] = PreCandidate
              /\ votesGranted[i] \in Quorum
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesSent' = [votesSent EXCEPT ![i] = FALSE ]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars, o3MissingLog>>


\* Leader i receives a client request to add v to the log.

\* @ No Need to change
ClientRequest(i) ==
    /\ state[i] = FullLeader
    /\ clientRequests < MaxClientRequests
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> Len(log[i]) + 1,
                     conf  |-> {}]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           \* Make sure that each request is unique, reduce state space to be explored
           /\ clientRequests' = clientRequests + 1
           \* Leader will not have out of order entries.
           /\ o3StartIndex' = [o3StartIndex EXCEPT ![i] = Len(newLog)]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, o3CommitIndexes, committedLog, committedLogDecrease>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.

PrintVal(id, exp)  ==  Print(<<id, exp>>, TRUE)

\* @ committed index is still the sequential end of it. 
AdvanceCommitIndex(i) ==
    /\ state[i] = FullLeader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           \* @ Check if index can be committed in o3 list
           AgreeO3(index) == {i} \cup {k \in Server : index \in o3MatchIndexes[i][k]}
           \* @ Check the committed o3 indexes.
           newO3CommitIndexes == IF Len(log[i]) - newCommitIndex > 0 THEN
                                    {index \in 1..(Len(log[i]) - newCommitIndex) : AgreeO3(index) \in Quorum}
                                 ELSE
                                    {}          
           \* @ Update the committed log.
           newCommittedSeqLog ==
              IF newCommitIndex > 1 THEN 
                  [ j \in 1..newCommitIndex |-> log[i][j] ] 
              ELSE 
                   << >>
           newCommittedO3Log == 
              IF newO3CommitIndexes /= {} THEN
                  [ j \in 1..Len(log[i]) - newCommitIndex |-> log[i][newCommitIndex + j] ] 
              ELSE 
                   << >>
           newCommittedLog == IF Len(newCommittedO3Log) > 0 THEN 
                                 newCommittedSeqLog \o newCommittedO3Log
                              ELSE 
                                 newCommittedSeqLog
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ committedLogDecrease' = \/ ( newCommitIndex < Len(committedLog) )
                                     \/ \E j \in 1..Len(committedLog) : committedLog[j] /= newCommittedLog[j]
          /\ committedLog' = newCommittedLog
          \* @ Push the committed log index ahead if o3 entires becomes sequential.
          /\ o3CommitIndexes' = [o3CommitIndexes EXCEPT ![i] = newO3CommitIndexes] 
    
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, clientRequests, o3MatchIndexes, o3StartIndex>>

----

FirstIndexOfTerm(i, thisTerm) ==
    CASE Len(log[i]) = 0 -> 0
      [] Len(log[i]) = 1 -> IF log[i][1].term = thisTerm THEN 1 ELSE 0
      [] OTHER -> LET allIndexes == [x \in 1..Len(log[i]) |-> x]
                      indexSeq ==  SelectSeq( allIndexes, LAMBDA x: log[i][x].term = thisTerm )
                  IN IF Len(indexSeq) > 0 THEN Head(indexSeq) ELSE 0

\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestPreVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestPreVoteRequest(i, j, m) ==
    \* Must satisfy the old condition
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        \* @ Extra condition (all the logs candidate needs has been sent) m.mo3NeedSync looks like {2, 3, 5, 7}
        o3LogNeedSyncIndexesCandidate == IF Cardinality(m.mo3NeedSync) = 0 THEN {} 
                                         ELSE {x \in m.mo3NeedSync: x <= Len(log[i]) /\ log[i][x].value /= Gap /\ log[i][x].term = m.mo3StartTerm}
        
        o3LogNeedSyncIndexes == IF Cardinality(o3LogNeedSyncIndexesCandidate) = 0 THEN 0
                                ELSE CHOOSE x \in o3LogNeedSyncIndexesCandidate: TRUE
        
        o3LogNeedSyncEntries == IF o3LogNeedSyncIndexes = 0 THEN Nil 
                                ELSE log[i][o3LogNeedSyncIndexes]
                                
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil}
                 /\ o3LogNeedSyncIndexes = 0 \* Fully sent
                 
        firstIndexLastTerm == FirstIndexOfTerm(i, LastTerm(log[i]))

    IN /\ m.mterm <= currentTerm[i]
       /\ Reply([mtype        |-> RequestPreVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j,
                 mlastLogTerm |-> LastTerm(log[i]), \* @ Tell candidate my last term to help it sync all my missed log before current term
                 mlastTermStartIndex   |-> firstIndexLastTerm,
                 mo3LogNeedSyncIndexes |-> o3LogNeedSyncIndexes,
                 mo3LogNeedSyncEntries |-> o3LogNeedSyncEntries],
                 m)
       /\ UNCHANGED votedFor
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>

\* @ There is no conflication
CheckReplace(entryA, entryB) ==
    IF entryA.value = Gap THEN entryB ELSE entryA

Merge(normalLog, o3Log, o3Indexes, o3LogTerm) ==
    IF o3Indexes > Len(normalLog) + 1 THEN 
        Append(normalLog, [term  |-> o3LogTerm, \* It only appears in current term (last term)
                           value |-> Gap,
                           conf  |-> {}])
    ELSE IF o3Indexes = Len(normalLog) + 1 THEN 
            Append(normalLog, o3Log)
         ELSE
            [normalLog EXCEPT ![o3Indexes] = CheckReplace(normalLog[o3Indexes], o3Log)]

HandleRequestFullVoteRequest(i, j, m) == 
    /\ LET 
           needSync == IF Len(log[i]) > 0 THEN 
                            {index \in Max({o3StartIndex[i], 1})..Len(log[i]) : log[i][index].value = Gap }
                       ELSE {}
           logOk == \/ /\ m.mprevLogIndex <= Len(log[i])
                       /\ \/ /\ m.mprevLogTerm = 0 
                          \/ /\ m.mprevLogTerm /= 0  \* Must in Sequence!
                             /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
                       /\ Len(m.mentries) = 1
                       /\ m.mentries[1].value = Conf
                       /\ \A index \in needSync : index \in m.mentries[1].conf \* check i have received all entries that need sync
                    \/ /\ m.mprevLogTerm = LastTerm(log[i]) 
                       /\ m.mprevLogIndex = Len(log[i]) + 1
                       /\ Len(m.mentries) = 0
           grant == /\ m.mterm = currentTerm[i]
                    /\ logOk
                    /\ votedFor[i] \in {Nil, j}
           vaildFill == /\ m.mprevLogIndex <= Len(log[i])
                        /\ Len(m.mentries) = 1
                        /\ \/ m.mprevLogIndex = 0
                           \/ m.mprevLogTerm = log[i][m.mprevLogIndex].term 
           newLog == IF grant /\ Len(m.mentries) = 1 /\ m.mentries[1].value = Conf /\ m.mprevLogIndex <= Len(log[i]) THEN \* apply the configuration (gaps)
                           Append(SubSeq(log[i], 1, m.mprevLogIndex) , m.mentries[1]) 
                     ELSE IF Len(m.mentries) = 1 /\ m.mentries[1].value /= Gap /\ vaildFill THEN 
                                Merge(log[i], m.mentries[1], m.mprevLogIndex + 1, m.mentries[1].term)
                          ELSE
                                log[i]
           mneedSync == IF vaildFill THEN m.mprevLogIndex + 2 ELSE o3StartIndex[i]
       IN  /\ m.mterm <= currentTerm[i]
           /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
              \/ ~grant /\ UNCHANGED votedFor
           /\ log' = [log EXCEPT ![i] = newLog]
           /\ Reply([mtype        |-> RequestFullVoteResponse,
                     mterm        |-> currentTerm[i],
                     mvoteGranted |-> grant,
                     mneedSync   |-> mneedSync,
                     \* mlog is used just for the `elections' history variable for
                     \* the proof. It would not exist in a real implementation.
                     mlog         |-> log[i],
                     msource      |-> i,
                     mdest        |-> j],
                     m)   
     /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, o3StartIndex, o3CommitIndexes, commitIndex, clientRequests, committedLog, committedLogDecrease>>
           
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].

\* @ Not sure server i can be elected. So here we only add the missing entries to our log, but not replace them.
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        \* @ we add the condition here, the last log index must be equal to candidate. 
        o3LogOk == \/ /\ m.mo3ToSyncEntries = Nil \* @ if candidate did not give me any entries
                      /\ m.mlastLogTerm = LastTerm(log[i]) 
                      /\ m.mlastLogIndex = Len(log[i]) \* @ the entries must be equal
\*                      /\ o3StartIndex[i] = Len(log[i]) \* @ it should not have any o3 entries 
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
                 /\ o3LogOk
        o3PrevLogTerm == IF m.mo3ToSyncIndexes = 1 THEN 0 ELSE log[i][m.mo3ToSyncIndexes - 1].term
        \* not vaild, need truncate
        nextSyncIndex == IF m.mo3lastLogTerm /= 0 /\ o3PrevLogTerm /= m.mo3lastLogTerm THEN
                              m.mo3ToSyncIndexes - 1
                         ELSE 
                              m.mo3ToSyncIndexes + 1
        newLog == IF ~ o3LogOk /\ logOk /\ m.mo3ToSyncIndexes > 0 /\ o3PrevLogTerm = m.mo3lastLogTerm THEN 
                       Merge(log[i], m.mo3ToSyncEntries, m.mo3ToSyncIndexes, m.mlastLogTerm)
                  ELSE IF m.mo3lastLogTerm /= 0 /\ o3PrevLogTerm /= m.mo3lastLogTerm THEN 
                          SubSeq(log[i], 1, nextSyncIndex) 
                       ELSE 
                          log[i]
        
    IN /\ m.mterm <= currentTerm[i]
\*       /\ o3StartIndex '= [o3StartIndex EXCEPT ![i] = newO3StartIndex]
       /\ log'= [log EXCEPT ![i] = newLog]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 mlastLogTerm |-> LastTerm(newLog), \* @ Tell candidate my last term to help it sync all my missed log before current term
                 mlastTermStartIndex   |-> FirstIndexOfTerm(i, LastTerm(newLog)),
                 mnextSyncIndex        |-> nextSyncIndex,
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, o3StartIndex, leaderVars, o3CommitIndexes, commitIndex, clientRequests, committedLog, committedLogDecrease>>

\* Server i receives a RequestPreVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestPreVoteResponse(i, j, m) ==
    LET newLog == IF m.mo3LogNeedSyncIndexes /= 0 /\ m.mterm = currentTerm[i] THEN
                        Merge(log[i], m.mo3LogNeedSyncEntries, m.mo3LogNeedSyncIndexes, m.mterm)
                  ELSE log[i]   \* log[i] length should be longer than log[j] here
    IN
        \* This tallies votes even when the current state is not PreCandidate, but
        \* they won't be looked at, so it doesn't matter.
        /\ m.mterm = currentTerm[i]
        \* @ must ensure it it PreCandidate, after it becomes candidate, the log should not be changed anymore. Otherwise the entries maybe change in sync process
        /\ state[i] = PreCandidate
        /\ log'= [log EXCEPT ![i] =  newLog]
        /\ o3MissingLog' = [o3MissingLog EXCEPT ![i][j] = m.mlastTermStartIndex + 1]
        /\ \/ /\ m.mvoteGranted
              /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                      votesGranted[i] \cup {j}]
              /\ voterLog' = [voterLog EXCEPT ![i] =
                                  voterLog[i] @@ (j :> m.mlog)]
              /\ UNCHANGED <<votesSent>>
           \/ /\ ~m.mvoteGranted
              /\ UNCHANGED <<votesSent, votesGranted, voterLog>>
        /\ Discard(m)
        /\ UNCHANGED <<serverVars, votedFor, leaderVars, o3StartIndex, o3CommitIndexes, commitIndex, clientRequests, committedLog, committedLogDecrease>>


\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Candidate
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
          /\ UNCHANGED <<votesSent, o3MissingLog>>
       \/ /\ ~m.mvoteGranted
          /\ o3MissingLog' = [o3MissingLog EXCEPT ![i][j] = Max({m.mnextSyncIndex, o3MissingLog[i][j]})]
          /\ UNCHANGED <<votesSent, votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>
    
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestFullVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Leader
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
          /\ UNCHANGED <<votesSent, o3MissingLog>>
       \/ /\ ~m.mvoteGranted
          /\ o3MissingLog' = [o3MissingLog EXCEPT ![i][j] = Max({m.mneedSync, o3MissingLog[i][j]})]
          /\ UNCHANGED <<votesSent, votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>
    
\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry. 
HandleAppendEntriesRequest(i, j, m) ==
    LET needSync == IF Len(log[i]) > 0 /\ m.mentries[1].value = Conf /\ m.mentries /= << >> THEN 
                         {index \in Max({o3StartIndex[i], 1})..m.mprevLogIndex 
                                : (index > Len(log[i]) \/ log[i][index].value = Gap) }
                    ELSE {}        
        \* if not config ok, then truncate   
        confOk == \/ /\ m.mentries /= << >> 
                     /\ \/ m.mentries[1].value /= Conf
                        \/ /\ m.mentries[1].value = Conf   
                           /\ \A index \in needSync : index \in m.mentries[1].conf \* check i have received all entries that need sync
                  \/ /\ m.mentries = << >> 
        logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
                    /\ confOk
                 \/ \* @ Added, it can also be accepted if this entry in same term but not in sequence.  
                    \* @ But, if they in different term, this cannot be accepted because this node doesn't have the 'term start' entry, 
                    \* @ i.e., don't know the out of order entries condition in last term
                    /\ m.mprevLogIndex > 0
                    /\ m.mprevLogTerm = LastTerm(log[i])
                    /\ confOk
       desperatedOk == \/ LastTerm(log[i]) = m.mterm
                       \/ /\ LastTerm(log[i]) < m.mterm
                          /\ m.mentries /= << >> 
                          /\ \/ /\ LastTerm(log[i]) = m.mentries[1].term
                                /\ \A index \in 1..Len(log[i]) : index \in m.mo3commitIndex \/ log[i][index].value = Gap
                             \/ /\ LastTerm(log[i]) > m.mentries[1].term
       newLog == IF desperatedOk \/ m.mentries = << >> THEN log[i] ELSE [index2 \in 1..Len(log[i]) |-> 
                                                                                IF index2 \in m.mo3commitIndex
                                                                                    \/ log[i][index2].term /= LastTerm(log[i])
                                                                                THEN
                                                                                    log[i][index2]
                                                                                ELSE
                                                                                    [term  |-> LastTerm(log[i]), 
                                                                                     value |-> Gap,
                                                                                     conf  |-> {}]]
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             \* @ need to check it then
             /\ m.mterm = currentTerm[i]
             /\ state[i] \in {PreCandidate, Candidate}
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(newLog) >= index
                             /\ newLog[index].term = m.mentries[1].term
                             \* @ in case of replicate on desperated entries !!! uncommitttd entries from old terms should be removed 
                             /\ newLog[index].term = m.mterm
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
                       /\ o3CommitIndexes' = [o3CommitIndexes EXCEPT ![i] =
                                                m.mo3commitIndex]
                       /\ LET o3Info == CheckO3StartPoint(i, newLog)
                              newO3StartIndex == o3Info[1]
                              newO3MatchIndex == o3Info[2] 
                              confEntries == {index1 \in 1..Len(newLog) : newLog[index1].value = Conf /\ index1 < commitIndex}
                              confirmedGaps == UNION {newLog[index2].conf: index2 \in confEntries}
                              tnewLog == [index3 \in 1..Len(newLog) |-> IF index3 \in confirmedGaps THEN [term  |-> newLog[index3].term, 
                                                                                                          value |-> ConfirmedGap,
                                                                                                          conf  |-> {}]
                                                                                                    ELSE newLog[index3]]
                          IN  /\ log' = [log EXCEPT ![i] = newLog]
                              /\ o3StartIndex' = [o3StartIndex EXCEPT ![i] = newO3StartIndex]
                              /\ Reply([mtype           |-> AppendEntriesResponse,
                                        mterm           |-> currentTerm[i],
                                        msuccess        |-> TRUE,
                                        mmatchIndex     |-> newO3StartIndex,
                                        mo3MatchIndex   |-> newO3MatchIndex,
                                        msource         |-> i,
                                        mdest           |-> j],
                                        m)
                       /\ UNCHANGED <<serverVars, serverVars, clientRequests, committedLog, committedLogDecrease>>
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ Len(newLog) >= index
                       /\ newLog[index].term /= m.mentries[1].term
                       /\ LET new == [index2 \in 1..(Len(newLog) - 1) |->
                                            newLog[index2]]
                              newO3StartIndex == CheckO3StartPoint(i, new)[1]
                          IN /\ log' = [log EXCEPT ![i] = new]
                             /\ o3StartIndex'  = [o3StartIndex EXCEPT ![i] = newO3StartIndex]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease, o3CommitIndexes>>
                   \/ \* @ Also, it can fill a gap of o3 log
                       /\ m.mentries /= << >>
                       /\ Len(newLog) >= index
                       /\ newLog[index].term = m.mentries[1].term
                       /\ newLog[index].value = Gap
                       \* @ Replace the empty entry
                       /\ LET tNewLog == [newLog EXCEPT ![index] = m.mentries[1]]
                          IN  log' = [log EXCEPT ![i] = tNewLog]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease, o3StartIndex, o3CommitIndexes>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(newLog) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(newLog, m.mentries[1])]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease, o3StartIndex, o3CommitIndexes>>
                   \/ \* @ o3 entry: append o3 entry
                       /\ m.mentries /= << >>
                       /\ Len(newLog) < m.mprevLogIndex
                       /\ LET newGaps == [index2 \in 1..(m.mprevLogIndex - Len(newLog)) |-> [term  |-> m.mprevLogTerm, 
                                                                                             value |-> Gap,
                                                                                             conf  |-> {}]]
                              newAppended == Append(newGaps, m.mentries[1])
                              new == newLog \o newAppended
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease, o3StartIndex, o3CommitIndexes>>
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
\*          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
          /\ o3MatchIndexes' = [o3MatchIndexes EXCEPT ![i][j] = m.mo3MatchIndex]
          /\ UNCHANGED <<nextIndex>>
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ UNCHANGED <<matchIndex, o3MatchIndexes>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestPreVoteRequest
          /\ HandleRequestPreVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestPreVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestPreVoteResponse(i, j, m)
       \/ /\ m.mtype = RequestFullVoteRequest
          /\ HandleRequestFullVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestFullVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestFullVoteResponse(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Defines how the variables may transition.
Next == /\  \/ \E i \in Server : Restart(i)
            \/ \E i \in Server : Timeout(i)
            \/ \E i, j \in Server : RequestPreVote(i, j)
            \/ \E i, j \in Server : RequestVote(i, j)
            \/ \E i, j \in Server : RequestFullVote(i, j)
            \/ \E i \in Server : BecomeCandidate(i)
            \/ \E i \in Server : BecomeLeader(i)
            \/ \E i \in Server : BecomeFullLeader(i)
            \/ \E i \in Server : ClientRequest(i)
            \/ \E i \in Server : AdvanceCommitIndex(i)
            \/ \E i, j \in Server : AppendEntries(i, j)
            \/ \E m \in ValidMessage(messages) : Receive(m)
            \/ \E m \in SingleMessage(messages) : DuplicateMessage(m)
            \/ \E m \in ValidMessage(messages) : DropMessage(m)
            \/ \E i \in Server : BecomeFullLeader(i)
           \* History variable that tracks every log ever:
        /\ allLogs' = allLogs 


\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* The following are a set of verification by jinlmsft@hotmail.com
BothLeader( i, j ) == 
    /\ i /= j
    /\ currentTerm[i] = currentTerm[j]
    /\ state[i] = Leader
    /\ state[j] = Leader

MoreThanOneLeader ==
    \E i, j \in Server : BothLeader( i, j ) 
    
PreLeaderElected == \E i \in Server : state[i] = Candidate

LeaderElected == \E i \in Server : state[i] = Leader

Misplaced == /\ \E index \in 1..Len(log["s3"]): (log["s3"][index].value /= Gap /\ log["s3"][index].value /= ConfirmedGap /\ log["s3"][index].value /= index /\ log["s3"][index].value /= Conf)


===============================================================================

\* Changelog:
\* 2022-07-31:
\* - Formalise CP-Raft out-of-order commit & apply mechanism.
\*
\* 2017-09-07:
\* - Formalise PreVote mechanism.
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
