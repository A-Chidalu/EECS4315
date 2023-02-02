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
        i := i + 1;
    }
  }
}
*)

=============================================================================
\* Modification History
\* Last modified Thu Feb 02 16:03:15 EST 2023 by chiddy00
\* Created Thu Feb 02 12:28:16 EST 2023 by chiddy00

Outside the range of checking - no effects.
Sometimes you may want to write written answers here.