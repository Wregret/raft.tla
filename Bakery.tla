------------------------------- MODULE Bakery -------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT ID
VARIABLES pc, at, atmp
\*VARIABLES pc, choosing, number
          
\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in {s[i]: i \in ID} : \A y \in {s[i]: i \in ID} : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in {s[i]: i \in ID} : \A y \in {s[i]: i \in ID} : x >= y

KeepOrder(before, after) == \A m,n \in ID:
                               CASE before[m] < before[n] -> after[m] < after[n]
                                 [] before[m] = before[n] -> after[m] = after[n]
                                 [] before[m] > before[n] -> after[m] > after[n]

IsOrdinalZero(x) == /\ Min(x) = 0
                    /\ \A i \in ID: x[i] \in Min(x)..Max(x)
                    /\ \A n \in Min(x)..Max(x): \E i \in ID: x[i] = n
                    
ZeroSequence == {x \in [ID -> ID]: IsOrdinalZero(x)}


IsOrdinalOne(x) == /\ Min(x) = 1
                   /\ \A i \in ID: x[i] \in Min(x)..Max(x)
                   /\ \A n \in Min(x)..Max(x): \E i \in ID: x[i] = n
                   
OneSequence == {x \in [ID -> 1..Cardinality(ID)] : IsOrdinalOne(x)}

h(x) == IF 0 \in {x[i]: i \in ID}
        THEN CHOOSE zs \in ZeroSequence: KeepOrder(x, zs)
        ELSE CHOOSE os \in OneSequence: KeepOrder(x, os)
        
RST(x, i) == h([x EXCEPT ![i] = 0])

SET(x, i, y, j) == h([x EXCEPT ![i] = y[j]])

INC1(x, i, y, j) == h([s \in ID |-> IF s = i THEN y[j] + 1
                                    ELSE IF x[s] <= y[j] THEN x[s]
                                         ELSE x[s] + 1])

INC2(x, i, y, j) == h([x EXCEPT ![i] = y[j] + 1])

Init == /\ pc = [i \in ID |-> 1]
        /\ at = [i \in ID |-> 0]
        /\ atmp = [i \in ID |-> 0]

Next == \E i \in ID:
        \/ /\ pc[i] = 1
           /\ \A j \in ID \ {i}: at[j] < Max(at)
           /\ \A j \in ID \ {i}: at[j] < Max(atmp)
           /\ atmp' = INC1(atmp, i, at, CHOOSE j \in ID \ {i}: TRUE)
           /\ pc' = [pc EXCEPT ![i] = 2]
           /\ UNCHANGED <<at>>
        \/ /\ pc[i] = 1
           /\ atmp' = INC2(atmp, i, at, CHOOSE j \in ID \ {i}: TRUE)
           /\ pc' = [pc EXCEPT ![i] = 2]
           /\ UNCHANGED <<at>>
        \/ /\ pc[i] = 2
           /\ at' = SET(at, i, atmp, i)
           /\ pc' = [pc EXCEPT ![i] = 3]
           /\ UNCHANGED <<atmp>>
        \/ /\ pc[i] = 3
           /\ \/ \A j \in ID \ {i}: at[j] = 0
              \/ \A j \in ID \ {i}: atmp[i] < at[j]
              \/ \A j \in ID \ {i}: /\ atmp[i] = at[j]
                                    /\ i = 0
           /\ pc' = [pc EXCEPT ![i] = 4]
           /\ UNCHANGED <<at, atmp>>
        \/ /\ pc[i] = 4
           /\ at' = RST(at, i)
           /\ pc' = [pc EXCEPT ![i] = 1]
           /\ UNCHANGED <<atmp>>
 
 TypeOK == /\ at \in [ID -> 0..Cardinality(ID)]
           /\ atmp \in [ID -> 0..Cardinality(ID)]
           /\ pc \in [ID -> {1, 2, 3, 4}]


=============================================================================
\* Modification History
\* Last modified Tue Jun 09 18:41:40 EDT 2020 by wregret
\* Created Fri May 22 00:20:13 EDT 2020 by wregret
