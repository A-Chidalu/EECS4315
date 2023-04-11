--------------------------- MODULE getAllPrefixes ---------------------------

EXTENDS Integers, Sequences, TLC
CONSTANT input


\* Get al prefixes of a tuple input

(*

    --algorithm getAllPrefixes {
        variable output = input, i = 1, j = 1, dummy = << >>;
        
        
        \* main method
        {
        
            while(i <= Len(input)){
                dummy := << >>;
                
                
                j := 1;
                
                while(j <= i){
                    
                    dummy := Append(dummy, input[j]);
                
                
                
                    j := j + 1;
                };
                
                output[i] := dummy;
                
                
                
                i := i + 1;
            };
            
            
            assert \A x \in 1..Len(input):(
            \A y \in 1..Len(output[x]): output[x][y] = input[y]
            );
           
            
        
        
        }
        
    
    
    
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e60698ac" /\ chksum(tla) = "62d456ee")
VARIABLES output, i, j, dummy, pc

vars == << output, i, j, dummy, pc >>

Init == (* Global variables *)
        /\ output = input
        /\ i = 1
        /\ j = 1
        /\ dummy = << >>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i <= Len(input)
               THEN /\ dummy' = << >>
                    /\ j' = 1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(       \A x \in 1..Len(input):(
                              \A y \in 1..Len(output[x]): output[x][y] = input[y]
                              ), 
                              "Failure of assertion at line 41, column 13.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << j, dummy >>
         /\ UNCHANGED << output, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF j <= i
               THEN /\ dummy' = Append(dummy, input[j])
                    /\ j' = j + 1
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED << output, i >>
               ELSE /\ output' = [output EXCEPT ![i] = dummy]
                    /\ i' = i + 1
                    /\ pc' = "Lbl_1"
                    /\ UNCHANGED << j, dummy >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Mar 07 17:16:03 EST 2023 by chiddy00
\* Created Tue Mar 07 15:04:55 EST 2023 by chiddy00
