------------------------ MODULE raft_leader_election ------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Server
CONSTANT Follower, Candidate, Leader
CONSTANT Nil
CONSTANT True, False
CONSTANT RequestVoteRequest, RequestVoteResponse

VARIABLES votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, network, voteGotten, voteResponded
\*VARIABLES votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, voteGotten

----
\* Finitification *\
Min(s) == CHOOSE x \in {s[i]: i \in Server} : \A y \in {s[i]: i \in Server} : x <= y
Max(s) == CHOOSE x \in {s[i]: i \in Server} : \A y \in {s[i]: i \in Server} : x >= y

KeepOrder(before, after) == \A m,n \in Server:
                               CASE before[m] < before[n] -> after[m] < after[n]
                                 [] before[m] = before[n] -> after[m] = after[n]
                                 [] before[m] > before[n] -> after[m] > after[n]

IsOrdinalZero(x) == /\ Min(x) = 0
                    /\ \A i \in Server: x[i] \in Min(x)..Max(x)
                    /\ \A n \in Min(x)..Max(x): \E i \in Server: x[i] = n
                    
ZeroSequence == {x \in [Server -> Server]: IsOrdinalZero(x)}


IsOrdinalOne(x) == /\ Min(x) = 1
                   /\ \A i \in Server: x[i] \in Min(x)..Max(x)
                   /\ \A n \in Min(x)..Max(x): \E i \in Server: x[i] = n
                   
OneSequence == {x \in [Server -> 1..Cardinality(Server)] : IsOrdinalOne(x)}

h(x) == IF 0 \in {x[i]: i \in Server}
            THEN x' = CHOOSE zs \in ZeroSequence: KeepOrder(x, zs)
            ELSE x' = CHOOSE os \in OneSequence: KeepOrder(x, os)
        
RST(x, i) == h([x EXCEPT ![i] = 0])

SET(x, i, j) == h([x EXCEPT ![i] = x[j]])

INC1(x, i, j) == h([s \in Server |-> IF s = i THEN x[j] + 1
                                 ELSE IF x[s] <= x[j] THEN x[s]
                                      ELSE x[s] + 1])

INC2(x, i, j) == h([x EXCEPT ![i] = x[j] + 1])

INC(x, i, j) == \/ /\ x[i] < Max(x)
                   /\ INC1(x, i, j)
                \/ INC2(x, i, j)

----
\* Quorum *\
\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

----
\* Network *\

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == network' = WithMessage(m, network)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == network' = WithoutMessage(m, network)

\* Combination of Send and Discard
Reply(response, request) ==
    network' = WithoutMessage(request, WithMessage(response, network))

----
\* RPC: i -> j *\
RequestVote(i, j) == /\ status[i] = Candidate
                     /\ j \notin voteResponded[i]
                     /\ Send([msender |-> i, 
                              mreceiver |-> j,
                              mtype |-> RequestVoteRequest,
                              mterm |-> currentTerm[i],
                              mcandidateId |-> i,
                              mlastLogIndex |-> lastLogIndex[i],
                              mlastLogTerm |-> lastLogTerm[i]])
                     /\ UNCHANGED <<votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, voteGotten, voteResponded>>

----
\* Handler: i <- j*\

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) == LET logOK == \/ m.mlastLogTerm > lastLogTerm[i] \*problem here
                                                  \/ /\ m.mlastLogTerm = lastLogTerm[i]
                                                     /\ m.mlastLogIndex >= lastLogIndex[i]
                                         grant == /\ m.mterm = currentTerm[i] \*problem here
                                                  /\ logOK
                                                  /\ votedFor[i] = Nil
                                     IN /\ m.mterm <= currentTerm[i]
                                        /\ \/ grant /\ votedFor' = [votedFor EXCEPT ![i] = j]
                                           \/ ~grant /\ UNCHANGED votedFor
                                        /\ Reply([mtype |-> RequestVoteResponse,
                                                  mterm |-> currentTerm[i],
                                                  mvoteGranted |-> grant,
                                                  msender |-> i,
                                                  mreceiver |-> j],m)


\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
\* This tallies votes even when the current state is not Candidate, but
\* they won't be looked at, so it doesn't matter.
HandleRequestVoteResponse(i, j, m) == /\ m.mterm = currentTerm[i]
                                      /\ voteResponded' = [voteResponded EXCEPT ![i] = voteResponded[i] \cup {j}]
                                      /\ \/ /\ m.mvoteGranted
                                            /\ voteGotten' = [voteGotten EXCEPT ![i] = voteGotten[i] + 1]
                                         \/ /\ ~m.mvoteGranted
                                            /\ UNCHANGED <<voteGotten>>
                                      /\ Discard(m)
                                      /\ UNCHANGED<<votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ SET(currentTerm, i, m.sender) \*problem here
    /\ status' = [status EXCEPT ![i] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
       \* network is unchanged so m can be processed further.
    /\ UNCHANGED <<lastLogIndex, lastLogTerm, cluster, network, voteGotten, voteResponded>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, voteGotten, voteResponded>>
    
\* Receive a message.
Receive(m) == LET i == m.mreceiver
                  j == m.msender
              IN \* Any RPC with a newer term causes the recipient to advance
                 \* its term first. Responses with stale terms are ignored.
                 \/ UpdateTerm(i, j, m)
                 \/ /\ m.mtype = RequestVoteRequest
                    /\ HandleRequestVoteRequest(i, j, m)
                 \/ /\ m.mtype = RequestVoteResponse
                    /\ \/ DropStaleResponse(i, j, m)
                       \/ HandleRequestVoteResponse(i, j, m)

----
\* Common Behavior *\
Timeout(i) == /\ status[i] \in {Follower, Candidate}
              /\ status' = [status EXCEPT ![i] = Candidate]
              /\ INC(currentTerm, i, i)
              /\ votedFor' = [votedFor EXCEPT ![i] = i]
              /\ voteGotten' = [voteGotten EXCEPT ![i] = 1]
              /\ voteResponded' = [voteResponded EXCEPT ![i] = {}]
              /\ UNCHANGED <<lastLogIndex, lastLogTerm, cluster, network>>

BecomeLeader(i) == /\ voteGotten[i] * 2 > Cardinality(Server)
                   /\ status[i] = Candidate
                   /\ status' = [status EXCEPT ![i] = Leader]
                   /\ UNCHANGED <<votedFor, currentTerm, lastLogIndex, lastLogTerm, cluster, network, voteGotten, voteResponded>>

\*ReplyRequestVote(i) == LET pending == {rpc \in network: (i \in rpc[receiver] /\ rpc[type] = RequestVoteRequest)}
\*                       IN IF Cardinality(pending) > 0
\*                          THEN LET rpc == CHOOSE p \in pending: TRUE
\*                               IN /\ IF rpc[term] < currentTerm[i]
\*                                     THEN /\ reply = {[sender |-> i,
\*                                                       receiver |-> rpc.sender,
\*                                                       type |-> RequestVoteReply,
\*                                                       term |-> currentTerm[i],
\*                                                       voteGranted |-> False]}
\*                                          /\ UNCHANGED<<currentTerm, votedFor, status>>
\*                                     ELSE /\ SET(currentTerm, i, rpc[sender]) \* problem here
\*                                          /\ IF votedFor[i] = Nil
\*                                             THEN /\ IF rpc[term] > currentTerm[i]
\*                                                     THEN status' = [status EXCEPT ![i] = Follower]
\*                                                     ELSE UNCHANGED<<status>>
\*                                                  /\ IF rpc[LLT] > lastLogTerm[i]
\*                                                     THEN /\ reply = {[sender |-> i,
\*                                                                       receiver |-> rpc[sender],
\*                                                                       type |-> RequestVoteReply,
\*                                                                       term |-> rpc[term],
\*                                                                       voteGranted |-> True]}
\*                                                          /\ votedFor' = [votedFor EXCEPT ![i] = rpc[sender]]
\*                                                     ELSE IF (rpc[LLT] = lastLogTerm[i] /\ rpc[LLI] >= lastLogIndex[i])
\*                                                          THEN /\ reply = {[sender |-> i,
\*                                                                      receiver |-> rpc[sender],
\*                                                                      type |-> RequestVoteReply,
\*                                                                      term |-> rpc[term],
\*                                                                      voteGranted |-> True]}
\*                                                               /\ votedFor' = [votedFor EXCEPT ![i] = rpc[sender]]
\*                                                          ELSE /\ reply = {[sender |-> i,
\*                                                                      receiver |-> rpc[sender],
\*                                                                      type |-> RequestVoteReply,
\*                                                                      term |-> rpc[term],
\*                                                                      voteGranted |-> False]}
\*                                                               /\ UNCHANGED<<votedFor>>
\*                                              ELSE /\ reply = {[sender |-> i,
\*                                                       receiver |-> rpc[sender],
\*                                                       type |-> RequestVoteReply,
\*                                                       term |-> currentTerm[i],
\*                                                       voteGranted |-> False]}
\*                                                   /\ UNCHANGED<<votedFor, status>>
\*                                   /\ network' = (network \ rpc) \cup reply
\*                                   /\ UNCHANGED<<lastLogIndex, lastLogTerm, cluster, voteGotten>>
\*                           ELSE UNCHANGED<<votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, network, voteGotten>>
\*
\*GatherVote(i) == LET pending == {rpc \in network: (i \in rpc[receiver] /\ rpc[type] = RequestVoteReply)}
\*                 IN IF Cardinality(pending) > 0
\*                    THEN LET rpc == CHOOSE p \in pending: TRUE
\*                         IN /\ IF currentTerm[i] < rpc[term]
\*                               THEN /\ SET(currentTerm, i, rpc[sender]) \* problem here.
\*                                    /\ status' = [status EXCEPT ![i] = Follower]
\*                                    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
\*                                    /\ voteGotten' = [voteGotten EXCEPT ![i] = 0]
\*                               ELSE /\ IF rpc[voteGranted] = True
\*                                       THEN voteGotten' = [voteGotten EXCEPT ![i] = voteGotten[i] + 1]
\*                                       ELSE UNCHANGED<<voteGotten>>
\*                                    /\ UNCHANGED<<status, votedFor, currentTerm>>
\*                            /\ network' = network \ {rpc}
\*                    ELSE UNCHANGED<<votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, network, voteGotten>>
\*
\*Disconnect(i) == /\ cluster' = cluster \ {i}
\*                 /\ UNCHANGED <<votedFor, currentTerm, lastLogIndex, lastLogTerm, status, network, voteGotten>>
\*
\*Reconnect(i) == /\ cluster' = cluster \union {i}
\*                /\ UNCHANGED <<votedFor, currentTerm, lastLogIndex, lastLogTerm, status, network, voteGotten>>
\*
\*Disconnect(i) == /\ cluster' = cluster \ {i}
\*                 /\ UNCHANGED <<votedFor, currentTerm, lastLogIndex, lastLogTerm, status>>
\*
\*Reconnect(i) == /\ cluster' = cluster \union {i}
\*                /\ UNCHANGED <<votedFor, currentTerm, lastLogIndex, lastLogTerm, status>>
\*
\*Timeout(i) == /\ IF status[i] = Follower
\*                 THEN /\ status' = [status EXCEPT ![i] = Candidate]
\*                      /\ currentTerm' = INC(currentTerm, i, i)
\*                      /\ votedFor' = [votedFor EXCEPT ![i] = i]
\*                      /\ voteGotten = [voteGotten EXCEPT ![i] = 1]
\*                      /\ sendRequestVote(i)
\*                 ELSE UNCHANGED <<status, currentTerm, votedFor, voteGotten>>
\*              /\ UNCHANGED <<lastLogIndex, lastLogTerm, cluster>>


----
Init == /\ currentTerm = [i \in Server |-> 0]
        /\ votedFor = [i \in Server |-> Nil]
        /\ lastLogIndex = [i \in Server |-> 0]
        /\ lastLogTerm = [i \in Server |-> 0]
        /\ status = [i \in Server |-> Follower]
        /\ cluster = {i: i \in Server}
        /\ network = [m \in {} |-> 0]
        /\ voteGotten = [i \in Server |-> 0]
        /\ voteResponded = [i \in Server |-> {}]

Next == \/ \E i \in Server: Timeout(i)
        \/ \E i,j \in Server: RequestVote(i,j)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E m \in DOMAIN network : Receive(m)
\*        \/ \E m \in DOMAIN network : DuplicateMessage(m)
\*        \/ \E m \in DOMAIN network : DropMessage(m)

----
\* Properties *\
LeaderElected == <> (\E i \in Server: status[i] = Leader)
SingleLeader == [] \/ Cardinality({i \in Server: status[i] = Leader}) = 1
                   \/ Cardinality({i \in Server: status[i] = Leader}) = 0

=============================================================================
\* Modification History
\* Last modified Mon Jul 13 11:11:44 EDT 2020 by wregret
\* Created Sun Jul 05 11:45:52 EDT 2020 by wregret
