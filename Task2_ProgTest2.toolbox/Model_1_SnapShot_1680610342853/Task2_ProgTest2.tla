-------------------------- MODULE Task2_ProgTest2 --------------------------
EXTENDS Integers, Sequences, TLC, Naturals
CONSTANT input

(*
    --algorithm Task2_ProgTest2 {
        variable output = input;
        
        
        \* main method
        {
        
            assert \E x,y \in 1..Len(output) : 
            (\A a \in 1..(x-1) : output[a] % 3 = 0) 
            /\
            (\A b \in x..(y-1) : output[b] % 3 = 1) 
            /\
            (\A c \in y..Len(output) : output[c] % 3 = 2);
            
            
        }
    
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "fe9f814a" /\ chksum(tla) = "3115383b")
VARIABLES output, pc

vars == << output, pc >>

Init == (* Global variables *)
        /\ output = input
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(       \E x,y \in 1..Len(output) :
                   (\A a \in 1..(x-1) : output[a] % 3 = 0)
                   /\
                   (\A b \in x..(y-1) : output[b] % 3 = 1)
                   /\
                   (\A c \in y..Len(output) : output[c] % 3 = 2), 
                   "Failure of assertion at line 13, column 13.")
         /\ pc' = "Done"
         /\ UNCHANGED output

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Apr 04 08:10:56 EDT 2023 by chiddy00
\* Created Tue Apr 04 07:58:14 EDT 2023 by chiddy00
