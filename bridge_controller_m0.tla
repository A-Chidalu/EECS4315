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
    n := n + 1; \* Think of this like BAP or assignment
    return;
  }
  
  procedure ML_in() {
    n := n - 1;
    return;
  }
  
  \* main method
  {
    \* # iterations: bound
    while(i < bound) {
        \* Use the choice operator to simulate the selection of event by some central controller
        (*
            When multiple conditions are satisfied, it is non-deterministic as to which will be executed
        *)
        either { 
            if(TRUE) { 
                call ML_out(); 
            }; 
        }
        or { 
            if(TRUE) { 
                call ML_in(); 
             }; 
        };
        i := i + 1;
    }
  }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "68bd219" /\ chksum(tla) = "277340eb")
VARIABLES n, i, pc, stack

vars == << n, i, pc, stack >>

Init == (* Global variables *)
        /\ n = 0
        /\ i = 0
        /\ stack = << >>
        /\ pc = "Lbl_3"

Lbl_1 == /\ pc = "Lbl_1"
         /\ n' = n + 1
         /\ pc' = Head(stack).pc
         /\ stack' = Tail(stack)
         /\ i' = i

ML_out == Lbl_1

Lbl_2 == /\ pc = "Lbl_2"
         /\ n' = n - 1
         /\ pc' = Head(stack).pc
         /\ stack' = Tail(stack)
         /\ i' = i

ML_in == Lbl_2

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF i < bound
               THEN /\ \/ /\ IF TRUE
                                THEN /\ stack' = << [ procedure |->  "ML_out",
                                                      pc        |->  "Lbl_4" ] >>
                                                  \o stack
                                     /\ pc' = "Lbl_1"
                                ELSE /\ pc' = "Lbl_4"
                                     /\ stack' = stack
                       \/ /\ IF TRUE
                                THEN /\ stack' = << [ procedure |->  "ML_in",
                                                      pc        |->  "Lbl_4" ] >>
                                                  \o stack
                                     /\ pc' = "Lbl_2"
                                ELSE /\ pc' = "Lbl_4"
                                     /\ stack' = stack
               ELSE /\ pc' = "Done"
                    /\ stack' = stack
         /\ UNCHANGED << n, i >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ i' = i + 1
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << n, stack >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == ML_out \/ ML_in \/ Lbl_3 \/ Lbl_4
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Feb 04 10:41:35 EST 2023 by chiddy00
\* Created Thu Feb 02 12:28:16 EST 2023 by chiddy00

Outside the range of checking - no effects.
Sometimes you may want to write written answers here.
