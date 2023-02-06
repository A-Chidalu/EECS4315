------------------------ MODULE bridge_controller_m1 ------------------------
EXTENDS Integers, Naturals, Sequences, TLC
CONSTANT d, bound (* bound denotes the length of interleaving events *)
AXIOM /\ d \in Nat 
      /\ d > 0

\* Here we model the dynamic part of the module: algorithm
\* What's included in the algorithm will be translated into TLA state machine
(*
--algorithm bridgeController_m0 {
  variable a = 0, b = 0, c = 0, n = 0, i = 0;
  
  procedure ML_out() {
    ML_out_action: a := a + 1;
    return;
  }
  
  procedure ML_in() {
    ML_in_action: c := c - 1;
    return;
  }
  
  procedure IL_in() {
    IL_in_action_changing_a: a := a - 1;
    IL_in_action_changing_b: b := b + 1;
    return;
  }
  
  procedure IL_out() {
    IL_out_action_changing_b: b := b - 1;
    IL_out_action_changing_c: c := c - 1;
    return;
  }
  
  \* main method
  {
    loop: while(i < bound) {
        choice: either { 
            ML_out_guard: if(/\ (a + b < d) /\ (c = 0)) { 
                ML_out_occurs: call ML_out(); 
            }; 
        }
        or { 
            ML_in_guard: if(c > 0) { 
                ML_in_occurs: call ML_in(); 
             }; 
        }
        or { 
            IL_in_guard: if(a > 0) { 
                IL_in_occurs: call IL_in(); 
             }; 
        }
        or { 
            IL_out_guard: if(/\ b > 0 /\ a = 0) { 
                IL_out_occurs: call IL_out(); 
             }; 
        };
        progress: i := i + 1;
    }
  }
  
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8b8b6082" /\ chksum(tla) = "811481bb")
VARIABLES a, b, c, n, i, pc, stack

vars == << a, b, c, n, i, pc, stack >>

Init == (* Global variables *)
        /\ a = 0
        /\ b = 0
        /\ c = 0
        /\ n = 0
        /\ i = 0
        /\ stack = << >>
        /\ pc = "loop"

ML_out_action == /\ pc = "ML_out_action"
                 /\ a' = a + 1
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << b, c, n, i >>

ML_out == ML_out_action

ML_in_action == /\ pc = "ML_in_action"
                /\ c' = c - 1
                /\ pc' = Head(stack).pc
                /\ stack' = Tail(stack)
                /\ UNCHANGED << a, b, n, i >>

ML_in == ML_in_action

IL_in_action_changing_a == /\ pc = "IL_in_action_changing_a"
                           /\ a' = a - 1
                           /\ pc' = "IL_in_action_changing_b"
                           /\ UNCHANGED << b, c, n, i, stack >>

IL_in_action_changing_b == /\ pc = "IL_in_action_changing_b"
                           /\ b' = b + 1
                           /\ pc' = Head(stack).pc
                           /\ stack' = Tail(stack)
                           /\ UNCHANGED << a, c, n, i >>

IL_in == IL_in_action_changing_a \/ IL_in_action_changing_b

IL_out_action_changing_b == /\ pc = "IL_out_action_changing_b"
                            /\ b' = b - 1
                            /\ pc' = "IL_out_action_changing_c"
                            /\ UNCHANGED << a, c, n, i, stack >>

IL_out_action_changing_c == /\ pc = "IL_out_action_changing_c"
                            /\ c' = c - 1
                            /\ pc' = Head(stack).pc
                            /\ stack' = Tail(stack)
                            /\ UNCHANGED << a, b, n, i >>

IL_out == IL_out_action_changing_b \/ IL_out_action_changing_c

loop == /\ pc = "loop"
        /\ IF i < bound
              THEN /\ pc' = "choice"
              ELSE /\ pc' = "Done"
        /\ UNCHANGED << a, b, c, n, i, stack >>

choice == /\ pc = "choice"
          /\ \/ /\ pc' = "ML_out_guard"
             \/ /\ pc' = "ML_in_guard"
             \/ /\ pc' = "IL_in_guard"
             \/ /\ pc' = "IL_out_guard"
          /\ UNCHANGED << a, b, c, n, i, stack >>

ML_out_guard == /\ pc = "ML_out_guard"
                /\ IF /\ (a + b < d) /\ (c = 0)
                      THEN /\ pc' = "ML_out_occurs"
                      ELSE /\ pc' = "progress"
                /\ UNCHANGED << a, b, c, n, i, stack >>

ML_out_occurs == /\ pc = "ML_out_occurs"
                 /\ stack' = << [ procedure |->  "ML_out",
                                  pc        |->  "progress" ] >>
                              \o stack
                 /\ pc' = "ML_out_action"
                 /\ UNCHANGED << a, b, c, n, i >>

ML_in_guard == /\ pc = "ML_in_guard"
               /\ IF c > 0
                     THEN /\ pc' = "ML_in_occurs"
                     ELSE /\ pc' = "progress"
               /\ UNCHANGED << a, b, c, n, i, stack >>

ML_in_occurs == /\ pc = "ML_in_occurs"
                /\ stack' = << [ procedure |->  "ML_in",
                                 pc        |->  "progress" ] >>
                             \o stack
                /\ pc' = "ML_in_action"
                /\ UNCHANGED << a, b, c, n, i >>

IL_in_guard == /\ pc = "IL_in_guard"
               /\ IF a > 0
                     THEN /\ pc' = "IL_in_occurs"
                     ELSE /\ pc' = "progress"
               /\ UNCHANGED << a, b, c, n, i, stack >>

IL_in_occurs == /\ pc = "IL_in_occurs"
                /\ stack' = << [ procedure |->  "IL_in",
                                 pc        |->  "progress" ] >>
                             \o stack
                /\ pc' = "IL_in_action_changing_a"
                /\ UNCHANGED << a, b, c, n, i >>

IL_out_guard == /\ pc = "IL_out_guard"
                /\ IF /\ b > 0 /\ a = 0
                      THEN /\ pc' = "IL_out_occurs"
                      ELSE /\ pc' = "progress"
                /\ UNCHANGED << a, b, c, n, i, stack >>

IL_out_occurs == /\ pc = "IL_out_occurs"
                 /\ stack' = << [ procedure |->  "IL_out",
                                  pc        |->  "progress" ] >>
                              \o stack
                 /\ pc' = "IL_out_action_changing_b"
                 /\ UNCHANGED << a, b, c, n, i >>

progress == /\ pc = "progress"
            /\ i' = i + 1
            /\ pc' = "loop"
            /\ UNCHANGED << a, b, c, n, stack >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == ML_out \/ ML_in \/ IL_in \/ IL_out \/ loop \/ choice
           \/ ML_out_guard \/ ML_out_occurs \/ ML_in_guard \/ ML_in_occurs
           \/ IL_in_guard \/ IL_in_occurs \/ IL_out_guard \/ IL_out_occurs
           \/ progress
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

\* Begin coding the invariants
inv1_1 == a \in Nat
inv1_2 == b \in Nat
inv1_3 == c \in Nat
inv1_4 == a + b + c = n
inv1_5 == \/ a = 0 \/ c = 0

ML_out_event_guard == /\ a + b < d /\ c = 0
ML_in_event_guard == c > 0
IL_in_event_guard == a > 0
IL_out_event_guard == /\ b > 0 /\ a = 0

deadlock_free ==  \/ ML_out_event_guard \/ ML_in_event_guard \/ IL_in_event_guard \/ IL_out_event_guard

=============================================================================
\* Modification History
\* Last modified Sun Feb 05 18:12:01 EST 2023 by chiddy00
\* Created Sun Feb 05 16:49:03 EST 2023 by chiddy00
