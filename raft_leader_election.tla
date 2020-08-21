------------------------ MODULE raft_leader_election ------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Server
CONSTANT Follower, Candidate, Leader
CONSTANT Nil
CONSTANT True, False
CONSTANT RequestVoteRequest, RequestVoteResponse

VARIABLES votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, network, voteGotten, voteResponded
\*VARIABLES votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, voteGotten

\*VARIABLE counter

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
                    
ZeroSequence == {x \in [Server -> 0..Cardinality(Server)]: IsOrdinalZero(x)}


IsOrdinalOne(x) == /\ Min(x) = 1
                   /\ \A i \in Server: x[i] \in Min(x)..Max(x)
                   /\ \A n \in Min(x)..Max(x): \E i \in Server: x[i] = n
                   
OneSequence == {x \in [Server -> 1..Cardinality(Server)] : IsOrdinalOne(x)}

h(x) == IF 0 \in {x[i]: i \in Server}
            THEN CHOOSE zs \in ZeroSequence: KeepOrder(x, zs)
            ELSE CHOOSE os \in OneSequence: KeepOrder(x, os)
        
RST(x, i) == h([x EXCEPT ![i] = 0])

SET(x, i, j) == h([x EXCEPT ![i] = x[j]])

INC1(x, i, j) == h([s \in Server |-> IF s = i THEN x[j] + 1
                                 ELSE IF x[s] <= x[j] THEN x[s]
                                      ELSE x[s] + 1])

INC2(x, i, j) == h([x EXCEPT ![i] = x[j] + 1])

INC(x, i, j) == IF x[i] < Max(x)
                THEN CHOOSE inc \in {INC1(x, i, j), INC2(x, i, j)}: TRUE
                ELSE INC2(x, i, j)

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
        [msgs EXCEPT ![m] = 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = 0]
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
                     /\ j \in (Server \ voteResponded[i])
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
                                         grant == /\ currentTerm[j] >= currentTerm[i] \* unreal
                                                  /\ logOK
                                                  /\ votedFor[i] = Nil
                                     IN \* /\ m.mterm <= currentTerm[i]
                                        /\ \/ grant /\ votedFor' = [votedFor EXCEPT ![i] = j]
                                           \/ ~grant /\ UNCHANGED votedFor
                                        /\ Reply([mtype |-> RequestVoteResponse,
                                                  mterm |-> currentTerm[i],
                                                  mvoteGranted |-> grant,
                                                  msender |-> i,
                                                  mreceiver |-> j],m)
                                        /\ UNCHANGED<<lastLogIndex, lastLogTerm, cluster, currentTerm, status, voteGotten, voteResponded>>


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
    /\ currentTerm' = SET(currentTerm, i, m.msender) \* unreal
    /\ status' = [status EXCEPT ![i] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
       \* network is unchanged so m can be processed further.
    /\ UNCHANGED <<lastLogIndex, lastLogTerm, cluster, network, voteGotten, voteResponded>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
\*    /\ (m.mterm < currentTerm[i] \/ m.mterm > currentTerm[m.msender])
    /\ m.mterm > currentTerm[m.msender]
    /\ Discard(m)
    /\ UNCHANGED <<votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, voteGotten, voteResponded>>
    
\* Receive a message.
Receive(m) == /\ network[m] = 1
              /\ LET i == m.mreceiver
                     j == m.msender
                 IN \* Any RPC with a newer term causes the recipient to advance
                    \* its term first. Responses with stale terms are ignored.
                    \/ UpdateTerm(i, j, m)
                    \/ /\ m.mtype = RequestVoteRequest
                       /\ \/ DropStaleResponse(i, j, m)
                          \/ HandleRequestVoteRequest(i, j, m)
                    \/ /\ m.mtype = RequestVoteResponse
                       /\ \/ DropStaleResponse(i, j, m)
                          \/ HandleRequestVoteResponse(i, j, m)

----
\* Common Behavior *\
Timeout(i) == \* /\ {message \in DOMAIN network: message.mreceiver = i} = {} \* unreal
\*              /\ ~(\E s \in Server: status[s] \in {Leader})
              /\ status[i] \in {Follower, Candidate} \* unreal
              /\ status' = [status EXCEPT ![i] = Candidate]
              /\ currentTerm' = INC(currentTerm, i, i)
              /\ votedFor' = [votedFor EXCEPT ![i] = i]
              /\ voteGotten' = [voteGotten EXCEPT ![i] = 1]
              /\ voteResponded' = [voteResponded EXCEPT ![i] = {i}]
              /\ UNCHANGED <<lastLogIndex, lastLogTerm, cluster, network>>

BecomeLeader(i) == /\ voteGotten[i] * 2 > Cardinality(Server)
                   /\ status[i] = Candidate
                   /\ status' = [status EXCEPT ![i] = Leader]
                   /\ UNCHANGED <<votedFor, currentTerm, lastLogIndex, lastLogTerm, cluster, network, voteGotten, voteResponded>>

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
\*        /\ counter = 0
        
\*Next == /\ counter < 10
\*        /\ counter' = counter + 1
\*        /\ \/ \E i \in Server: Timeout(i)
\*           \/ \E i,j \in Server: RequestVote(i,j)
\*           \/ \E i \in Server : BecomeLeader(i)
\*           \/ \E m \in DOMAIN network : Receive(m)
\*        \/ \E m \in DOMAIN network : DuplicateMessage(m)
\*        \/ \E m \in DOMAIN network : DropMessage(m)

Next == \/ \E i \in Server: Timeout(i)
        \/ \E i,j \in Server: RequestVote(i,j)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E m \in DOMAIN network : Receive(m)
\*        \/ \E m \in DOMAIN network : DuplicateMessage(m)
\*        \/ \E m \in DOMAIN network : DropMessage(m)

\*Spec == Init /\ [][Next]_<<votedFor, currentTerm, lastLogIndex, lastLogTerm, status, cluster, network, voteGotten, voteResponded>>

----
\* Properties *\

IsNotLeader(i) == IF status[i] = Leader
                  THEN FALSE
                  ELSE TRUE
LeaderNotElected == [] (\A i \in Server: IsNotLeader(i))
LeaderElected == <> (\E i \in Server: status[i] = Leader)
\*SingleLeader == [] \/ Cardinality({i \in Server: status[i] = Leader}) = 1
\*                   \/ Cardinality({i \in Server: status[i] = Leader}) = 0

\* The following are a set of verification by jinlmsft@hotmail.com
BothLeader( i, j ) == 
    /\ i /= j
    /\ currentTerm[i] = currentTerm[j]
    /\ status[i] = Leader
    /\ status[j] = Leader

NoMoreThanOneLeader ==
    \E i, j \in Server :  ~BothLeader( i, j ) 

=============================================================================
\* Modification History
\* Last modified Fri Aug 21 11:08:49 EDT 2020 by wregret
\* Created Sun Jul 05 11:45:52 EDT 2020 by wregret
