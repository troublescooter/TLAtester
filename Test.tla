---- MODULE Test -----------------------------------------------------
EXTENDS Sequences, Naturals, TLC, Example
(* Documentation *)
(* This module builds a state machine that executes a sequence of tests. *)
(* In order to adapt to different module than 'Example', change 'Example' to the *)
(* module to test, adapt number of tests by adding T's in TestInit, and adapt the *)
(* operators Pre, Run and the sequence P according to example *)
--------------------------------------------------------------------------------
VARIABLE Tests, counter, done
testvars == <<Tests, counter, done>>

total == <<Tests, counter, done>> \o vars

T ==
    [state |-> 0,
    passed |-> "not tested"]

TestInit ==
    (* CHANGE: how many tests in total, for example three: *)
    /\ Tests = <<T,T,T>>
    /\ counter = 1
    /\ done = 0
    /\ Init

Pre ==
    /\ Tests[counter].state = 0
    (* CHANGE: add setup for different tests *)
    /\ \/ /\ counter = 1
          /\ q' = [q EXCEPT ![0] = <<1,2,3>>]
          /\ UNCHANGED additional
       \/ /\ counter = 2
          /\ additional' = 4
          /\ UNCHANGED q
       \/ /\ counter = 3
          (* /\ q' = [q EXCEPT ![0] = <<1,2,3>>] *)
          /\ UNCHANGED <<q,additional>>
    /\ Tests' = [Tests EXCEPT ![counter].state = 1]
    /\ UNCHANGED <<counter,done>>

Run ==
    /\ Tests[counter].state = 1
    (* CHANGE: Add operators/functions to test *)
    /\ \/ /\ counter = 1
          /\ TRUE
          /\ UNCHANGED vars
       \/ /\ counter = 2
          /\ Inc(additional)
          /\ UNCHANGED q
       \/ /\ counter = 3
          /\ Attach
          /\ UNCHANGED additional
    /\ Tests' = [Tests EXCEPT ![counter].state = 2]
    /\ UNCHANGED <<counter,done>>

(* CHANGE: Add a postcondition *)
Post1 ==
    /\ q[0] = <<1,2,3>>
Post2 ==
    /\ additional = 5
Post3 ==
    /\ q[0] = <<1,2,3,4>>
    /\ q[1] = <<>>
    /\ additional = 5
(* CHANGE: Add postcondition to P *)
P == <<Post1, Post2, Post3>>

Post ==
    /\ Tests[counter].state = 2
    /\ counter \in 1..Len(P)
    /\ UNCHANGED vars
    /\ Tests' = [Tests EXCEPT ![counter].passed = IF P[counter] THEN "passed"
                                                                ELSE "failed"]
    /\ IF counter = Len(Tests) THEN /\ done' = 1
                                    /\ UNCHANGED <<counter>>
                               ELSE /\ counter' = counter + 1
                                    /\ UNCHANGED <<done>>

Test ==
    \/ /\ done = 0
       /\ \/ Pre
          \/ /\ ~ ENABLED Pre
             /\ Tests[counter].state = 0
             /\ Print("Precondition not enabled, counter:", TRUE)
             /\ Print(counter, TRUE)
             /\ UNCHANGED <<Tests, counter>>
             /\ UNCHANGED vars
          \/ Run
          \/ /\ ~ ENABLED Run
             /\ Tests[counter].state = 1
             /\ Print("Run statement not enabled, counter:", TRUE)
             /\ Print(counter, TRUE)
             /\ UNCHANGED <<Tests, counter>>
             /\ UNCHANGED vars
          \/ Post
          \/ /\ ~ ENABLED Post
             /\ Tests[counter].state = 2
             /\ Print("Postcondition not enabled, counter:", TRUE)
             /\ Print(counter, TRUE)
             /\ UNCHANGED <<Tests, counter>>
             /\ UNCHANGED vars
    \/ /\ done = 1
       /\ \A i \in 1..Len(Tests) : /\ Print(i,TRUE)
                                   /\ Print(Tests[i].passed, TRUE)
       /\ done' = 2
       /\ UNCHANGED <<Tests, counter>>
       /\ UNCHANGED vars

TestSpec == TestInit /\ [][Test]_total
================================================================================
