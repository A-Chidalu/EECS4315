------------------------- MODULE atLeastOnePositive -------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT input


(*



    --algorithm atLeastOnePositive {
        variable i = 1, atLeastOne = FALSE;
    
    
        \* main method
        {
            
            
            while(i <= Len(input)){
            
                if(input[i] > 0){
                    atLeastOne := TRUE;
                    i := Len(input) + 1;
                };
            
            
                i := i + 1;
            };
        
            
            
            
            
            assert atLeastOne = TRUE => \E x \in 1..Len(input): input[x] > 0;
        }
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c45faf67" /\ chksum(tla) = "fa734aba")
VARIABLES i, atLeastOne, pc

vars == << i, atLeastOne, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ atLeastOne = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i <= Len(input)
               THEN /\ IF input[i] > 0
                          THEN /\ atLeastOne' = TRUE
                               /\ i' = Len(input) + 1
                          ELSE /\ TRUE
                               /\ UNCHANGED << i, atLeastOne >>
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(atLeastOne = TRUE => \E x \in 1..Len(input): input[x] > 0, 
                              "Failure of assertion at line 33, column 13.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << i, atLeastOne >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ i' = i + 1
         /\ pc' = "Lbl_1"
         /\ UNCHANGED atLeastOne

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Mar 06 21:23:07 EST 2023 by chiddy00
\* Created Mon Mar 06 21:18:58 EST 2023 by chiddy00
