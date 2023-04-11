---------------------------- MODULE isMonotonic ----------------------------
EXTENDS Integers, Sequences, Naturals, TLC
CONSTANT input


(*

    --algorithm isMonotonic{
        variable output = TRUE, i = 1;
        
        
        \* Main Method
        {
            \* If the length is 0 or one it is vacously monotonic
            if(Len(input) = 0 \/ Len(input) = 1){
                output := TRUE;
            }
            else {
                
                if(input[1] < input[Len(input)]) {
                    
                    while(i < Len(input)){
                        if(input[i] >= input[i + 1]){
                            output := FALSE;
                        };
                        
                        i := i + 1;
                    };
                }
                else {
                    while(i < Len(input)){
                        if(input[i] <= input[i + 1]){
                            output := FALSE;
                        };
                        
                        i := i + 1;
                    }; 
                };
           
            };
            
            
            
            assert (Len(input) = 0 \/ Len(input) = 1) => output = TRUE;
            
            assert output = TRUE <=> ((input[1] < input[Len(input)]) /\ (\A x \in 1..(Len(input)-1) : input[x] < input[x + 1])) 
                                       \/ ((input[1] > input[Len(input)]) /\ (\A x \in 1..(Len(input)-1) : input[x] > input[x + 1]));
            
        }
    
    
    
    
    }

*)
\* BEGIN TRANSLATION (chksum(pcal) = "d6547e97" /\ chksum(tla) = "8dcc25b8")
VARIABLES output, i, pc

vars == << output, i, pc >>

Init == (* Global variables *)
        /\ output = TRUE
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(input) = 0 \/ Len(input) = 1
               THEN /\ output' = TRUE
                    /\ pc' = "Lbl_4"
               ELSE /\ IF input[1] < input[Len(input)]
                          THEN /\ pc' = "Lbl_2"
                          ELSE /\ pc' = "Lbl_3"
                    /\ UNCHANGED output
         /\ i' = i

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i < Len(input)
               THEN /\ IF input[i] >= input[i + 1]
                          THEN /\ output' = FALSE
                          ELSE /\ TRUE
                               /\ UNCHANGED output
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Lbl_4"
                    /\ UNCHANGED << output, i >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF i < Len(input)
               THEN /\ IF input[i] <= input[i + 1]
                          THEN /\ output' = FALSE
                          ELSE /\ TRUE
                               /\ UNCHANGED output
                    /\ i' = i + 1
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Lbl_4"
                    /\ UNCHANGED << output, i >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ Assert((Len(input) = 0 \/ Len(input) = 1) => output = TRUE, 
                   "Failure of assertion at line 44, column 13.")
         /\ Assert(output = TRUE <=> ((input[1] < input[Len(input)]) /\ (\A x \in 1..(Len(input)-1) : input[x] < input[x + 1]))
                                       \/ ((input[1] > input[Len(input)]) /\ (\A x \in 1..(Len(input)-1) : input[x] > input[x + 1])), 
                   "Failure of assertion at line 46, column 13.")
         /\ pc' = "Done"
         /\ UNCHANGED << output, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Apr 04 11:04:02 EDT 2023 by chiddy00
\* Created Tue Apr 04 10:34:44 EDT 2023 by chiddy00
