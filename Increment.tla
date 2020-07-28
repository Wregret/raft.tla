----------------------------- MODULE Increment -----------------------------
EXTENDS Integers

VARIABLES ticker

Init == ticker = 0
Next == \/ /\ ticker = 0
           /\ ticker' = 1
        \/ /\ ticker = 2
           /\ ticker' = 0

NoMoreThanTwo == [](ticker < 2)
=============================================================================
\* Modification History
\* Last modified Tue Jul 28 00:20:51 EDT 2020 by wregret
\* Created Mon Jul 27 11:52:41 EDT 2020 by wregret
