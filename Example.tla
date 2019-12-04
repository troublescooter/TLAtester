---- MODULE Example ------------------------------------------------------------
EXTENDS Naturals, Sequences
(* Documentation *)
(* This is an example module to write tests for *)
--------------------------------------------------------------------------------
VARIABLES q, additional
vars == <<q, additional>>

Arg == {0,1}

Init ==
    /\ additional = 0
    /\ q = [a \in Arg |-> << >>]

Inc(a) == additional' = a + 1
Attach == q' = [q EXCEPT ![0] = Append(q[0],4)]

Next ==
    \/ \E i \in 0..10 : Inc(i)
    \/ Attach

Spec == Init /\ [][Next]_vars
================================================================================
