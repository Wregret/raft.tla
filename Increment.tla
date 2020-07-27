----------------------------- MODULE Increment -----------------------------
EXTENDS Integers

VARIABLES ticker

Init == ticker = 0
Next == ticker' = ticker + 1
=============================================================================
\* Modification History
\* Last modified Mon Jul 27 11:53:42 EDT 2020 by wregret
\* Created Mon Jul 27 11:52:41 EDT 2020 by wregret
