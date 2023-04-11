\* Given an input tuple, swap the first and last element of the tuple and return
\* a new tuple (output)


\* Write the appropriate precondiitions and post conditions of this algo

-------------------------- MODULE swapFirstAndLast --------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT input


(*

    --algorithm swapFirstAndLast {
        variable i = 1, tmp = 0, output = input;
        
        
        
        
        {
            
            \* Precondition: input has at least two elements
            assert Len(input) >= 2;
            
            
            tmp := output[i];
            output[i] := output[Len(output)];
            output[Len(output)] := tmp;
            
            
            
            
            
            
            
            
            \* Postcondition: The arrays will have swapped values
            assert input[i] = output[Len(input)] /\ input[Len(input)] = output[i];
            
            
            
        
        
        }
    
    
    
    }    
*)
\* BEGIN TRANSLATION (chksum(pcal) = "791f0ec5" /\ chksum(tla) = "b7817c11")
VARIABLES i, tmp, output, pc

vars == << i, tmp, output, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ tmp = 0
        /\ output = input
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Len(input) >= 2, 
                   "Failure of assertion at line 23, column 13.")
         /\ tmp' = output[i]
         /\ output' = [output EXCEPT ![i] = output[Len(output)]]
         /\ pc' = "Lbl_2"
         /\ i' = i

Lbl_2 == /\ pc = "Lbl_2"
         /\ output' = [output EXCEPT ![Len(output)] = tmp]
         /\ Assert(input[i] = output'[Len(input)] /\ input[Len(input)] = output'[i], 
                   "Failure of assertion at line 38, column 13.")
         /\ pc' = "Done"
         /\ UNCHANGED << i, tmp >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Mar 06 21:34:10 EST 2023 by chiddy00
\* Created Mon Mar 06 21:26:37 EST 2023 by chiddy00
