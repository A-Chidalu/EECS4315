------------------------------- MODULE isGeo -------------------------------
EXTENDS Integers, Sequences, Naturals, TLC
CONSTANT input


(*

    --algorithm isGeo{
        variable i = 0, output = TRUE, constant = 1;
        
        \*Main Method
        {
        
            if(Len(input) = 0 \/ Len(input) = 1){
                output := FALSE;
            }
            else {
                
                constant := input[2] \div input[1];
                
                i := 3;
                
                while(i < Len(input)){
                    
                    if((input[i + 1] \div input[i]) # constant){
                        output := FALSE;
                    };
                    
                    i := i + 1;
                  
                };
            };
            
        
            
        
            assert (Len(input) = 0 \/ Len(input) = 1) => output = FALSE;
            
            assert output = TRUE <=> (\A a,b \in 1..(Len(input)-1) : (b = a + 1 => input[b] \div input[a] = input[b + 1] \div input[b]));
        }
    
    
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "57fdd03c" /\ chksum(tla) = "6b1ff198")
VARIABLES i, output, constant, pc

vars == << i, output, constant, pc >>

Init == (* Global variables *)
        /\ i = 0
        /\ output = TRUE
        /\ constant = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(input) = 0 \/ Len(input) = 1
               THEN /\ output' = FALSE
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << i, constant >>
               ELSE /\ constant' = (input[2] \div input[1])
                    /\ i' = 3
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED output

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i < Len(input)
               THEN /\ IF (input[i + 1] \div input[i]) # constant
                          THEN /\ output' = FALSE
                          ELSE /\ TRUE
                               /\ UNCHANGED output
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Lbl_3"
                    /\ UNCHANGED << i, output >>
         /\ UNCHANGED constant

Lbl_3 == /\ pc = "Lbl_3"
         /\ Assert((Len(input) = 0 \/ Len(input) = 1) => output = FALSE, 
                   "Failure of assertion at line 37, column 13.")
         /\ Assert(output = TRUE <=> (\A a,b \in 1..(Len(input)-1) : (b = a + 1 => input[b] \div input[a] = input[b + 1] \div input[b])), 
                   "Failure of assertion at line 39, column 13.")
         /\ pc' = "Done"
         /\ UNCHANGED << i, output, constant >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Apr 03 21:27:45 EDT 2023 by chiddy00
\* Created Mon Apr 03 20:48:30 EDT 2023 by chiddy00
