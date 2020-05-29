------------------------------- MODULE Bakery -------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT ID
VARIABLES at
          
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
           

\*Init == /\ pc = [i \in ID |-> 1]
\*        /\ at = [i \in ID |-> 0]
\*        /\ atmp = [i \in ID |-> 0]
\*
\*Next == \E i \in ID:
\*        \/ /\ pc[i] = 1
\*           /\ at[1 - i] < Max(at)
\*           /\ at[1 - i] < Max(atmp)
\*           /\ INC1(at, atmp, i)
\*           /\ pc' = [pc EXCEPT ![i] = 2]
\*        \/ /\ pc[i] = 1
\*           /\ i \in ID
\*           /\ INC2(at, atmp, i)
\*           /\ pc' = [pc EXCEPT ![i] = 2]
\*        \/ /\ pc[i] = 2
\*           /\ i \in ID
\*           /\ SET(at, atmp, i)
\*           /\ pc' = [pc EXCEPT ![i] = 3]
\*        \/ /\ pc[i] = 3
\*           /\ \/ at[1 - i] = 0
\*              \/ atmp[i] < at[1 - i]
\*              \/ /\ atmp[i] = at[1 - 1]
\*                 /\ i = 0
\*           /\ pc' = [pc EXCEPT ![i] = 4]
\*        \/ /\ pc[i] = 4
\*           /\ RST(at, i)
\*           /\ pc' = [pc EXCEPT ![i] = 1]


=============================================================================
\* Modification History
\* Last modified Fri May 29 11:51:19 EDT 2020 by wregret
\* Created Fri May 22 00:20:13 EDT 2020 by wregret
