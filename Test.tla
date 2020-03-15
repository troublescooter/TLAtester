---- MODULE Test -----------------------------------------------------
EXTENDS Sequences, Naturals, TLC, Example
(* Documentation *)
(*This module builds a state machine that executes a sequence of tests.
In order to adapt to different module than ExampleToTest, change ExampleToTest to the
module to test, adapt number of tests n, and adapt the
operators Pre, Run and the sequence PList according to example *)
--------------------------------------------------------------------------------
VARIABLE counter, done, state, tests
testvars == <<counter, done, state, tests>>

total == <<counter, done, state, tests>> \o vars

(* how many tests to run in total *)
n == 1

TestInit ==
    /\ tests = <<>>
    /\ counter = 1
    /\ done = 0
    /\ state = 0
    /\ Init

Pre ==
    /\ state = 0
    (* CHANGE: add setup for different tests *)
    /\ \/ /\ counter = 1
          /\ q' = [q EXCEPT ![0] = <<1,2,3>>]
          /\ UNCHANGED additional
       \/ /\ counter = 2
          /\ additional' = 4
          /\ UNCHANGED q
       \/ /\ counter = 3
          /\ UNCHANGED <<q, additional>>
    /\ state' = 1
    /\ UNCHANGED <<counter, done, tests>>

Run ==
    /\ state = 1
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
    /\ state' = 2
    /\ UNCHANGED <<counter, done, tests>>

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
PList == <<Post1, Post2, Post3>>

Post ==
    /\ state = 2
    /\ counter \in 1..Len(PList)
    /\ UNCHANGED vars
    /\ tests' = tests \o <<IF PList[counter] THEN "passed" ELSE "failed">>
    /\ state' = 0
    /\ IF counter = n THEN /\ done' = 1
                           /\ UNCHANGED counter
                      ELSE /\ counter' = counter + 1
                           /\ UNCHANGED done

Test ==
    \/ /\ done = 0
       /\ \/ Pre
          \/ Run
          \/ Post
          \/ /\ \/ /\ ~ ENABLED Pre
                   /\ counter \in 1..n
                   /\ state = 0
                   /\ Print("Precondition not enabled, Test:", TRUE)
                \/ /\ ~ ENABLED Run
                   /\ counter \in 1..n
                   /\ state = 1
                   /\ Print("Run statement not enabled, Test:", TRUE)
                \/ /\ ~ ENABLED Post
                   /\ counter \in 1..n
                   /\ state = 2
                   /\ Print("Postcondition not enabled, Test:", TRUE)
             /\ Print(counter, TRUE)
             /\ done' = 2
             /\ UNCHANGED <<counter, state, tests, vars>>
    \/ /\ done = 1
       /\ done' = 2
       /\ UNCHANGED <<counter, state, tests, vars>>

TestSpec == TestInit /\ [][Test]_total
================================================================================
