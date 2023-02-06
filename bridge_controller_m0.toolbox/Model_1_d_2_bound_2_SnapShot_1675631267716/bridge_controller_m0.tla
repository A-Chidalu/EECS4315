Outside the range of checking - no effects.

------------------------ MODULE bridge_controller_m0 ------------------------

\* This is a single line comment
(*
This is a multi line comment - comment 1
This is a multi line comment - comment 2
*)

EXTENDS Integers, Naturals, Sequences, TLC
CONSTANT d, bound (* bound denotes the length of interleaving events *)
AXIOM /\ d \in Nat 
      /\ d > 0

\* Here we model the dynamic part of the module: algorithm
\* What's included in the algorithm will be translated into TLA state machine
(*
--algorithm bridgeController_m0 {
  variable n = 0, i = 0;
  
  procedure ML_out() {
    ML_out_action: n := n + 1; \* Think of this like BAP or assignment
    return;
  }
  
  procedure ML_in() {
    ML_in_action: n := n - 1;
    return;
  }
  
  \* main method
  {
    \* # iterations: bound
    loop: while(i < bound) {
        \* Use the choice operator to simulate the selection of event by some central controller
        (*
            When multiple conditions are satisfied, it is non-deterministic as to which will be executed
        *)
        choice: either { 
            ML_out_guard: if(n < d) { 
                ML_out_occurs: call ML_out(); 
            }; 
        }
        or { 
            ML_in_guard: if(n > 0) { 
                ML_in_occurs: call ML_in(); 
             }; 
        };
        progress: i := i + 1;
    }
  }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "d8d38596" /\ chksum(tla) = "6492b783")
VARIABLES n, i, pc, stack

vars == << n, i, pc, stack >>

Init == (* Global variables *)
        /\ n = 0
        /\ i = 0
        /\ stack = << >>
        /\ pc = "loop"

ML_out_action == /\ pc = "ML_out_action"
                 /\ n' = n + 1
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ i' = i

ML_out == ML_out_action

ML_in_action == /\ pc = "ML_in_action"
                /\ n' = n - 1
                /\ pc' = Head(stack).pc
                /\ stack' = Tail(stack)
                /\ i' = i

ML_in == ML_in_action

loop == /\ pc = "loop"
        /\ IF i < bound
              THEN /\ pc' = "choice"
              ELSE /\ pc' = "Done"
        /\ UNCHANGED << n, i, stack >>

choice == /\ pc = "choice"
          /\ \/ /\ pc' = "ML_out_guard"
             \/ /\ pc' = "ML_in_guard"
          /\ UNCHANGED << n, i, stack >>

ML_out_guard == /\ pc = "ML_out_guard"
                /\ IF n < d
                      THEN /\ pc' = "ML_out_occurs"
                      ELSE /\ pc' = "progress"
                /\ UNCHANGED << n, i, stack >>

ML_out_occurs == /\ pc = "ML_out_occurs"
                 /\ stack' = << [ procedure |->  "ML_out",
                                  pc        |->  "progress" ] >>
                              \o stack
                 /\ pc' = "ML_out_action"
                 /\ UNCHANGED << n, i >>

ML_in_guard == /\ pc = "ML_in_guard"
               /\ IF n > 0
                     THEN /\ pc' = "ML_in_occurs"
                     ELSE /\ pc' = "progress"
               /\ UNCHANGED << n, i, stack >>

ML_in_occurs == /\ pc = "ML_in_occurs"
                /\ stack' = << [ procedure |->  "ML_in",
                                 pc        |->  "progress" ] >>
                             \o stack
                /\ pc' = "ML_in_action"
                /\ UNCHANGED << n, i >>

progress == /\ pc = "progress"
            /\ i' = i + 1
            /\ pc' = "loop"
            /\ UNCHANGED << n, stack >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == ML_out \/ ML_in \/ loop \/ choice \/ ML_out_guard \/ ML_out_occurs
           \/ ML_in_guard \/ ML_in_occurs \/ progress
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

\* Add Boolean properties for model checking of invariants

inv0_1 == n \in Nat \* alternatively: /\ n \in Nat
inv0_2 == n <= d

\* Add Boolean properties for model checking deadlock freedom
\* Being deadlock free means there's at least one event that's enabled (i.e. at least one guard will always evaluate to true)

ML_out_event_guard == TRUE
ML_in_event_guard == TRUE

deadlock_free == ML_out_event_guard \/ ML_in_event_guard 

=============================================================================
\* Modification History
\* Last modified Mon Feb 06 01:20:38 EST 2023 by chiddy00
\* Created Thu Feb 02 12:28:16 EST 2023 by chiddy00

Outside the range of checking - no effects.
Sometimes you may want to write written answers here.
