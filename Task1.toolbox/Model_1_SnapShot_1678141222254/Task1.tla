------------------------------- MODULE Task1 -------------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT input1, input2

(*
    --algorithm Task1{
        variable i = 1, j = 1, output = << >>, inSecondInput = FALSE;
        
        {
            
            
            while(i <= Len(input1)) {
                
                
                j := i;
                inSecondInput := FALSE;
                while(j <= Len(input2)){
                    if(input1[i] = input2[j]) {
                        inSecondInput := TRUE;
                        j := Len(input2) + 1;
                    };
                    
                    j := j + 1;
                };
                
                
                if(inSecondInput = FALSE) {
                    output := output \o <<input1[i]>>;
                };
                
                
                
                i := i + 1;
            };
            
            
            assert \A x \in 1..Len(input2): ~(\E y \in 1..Len(input1): input1[y] = input2[x]);
            
            
        }
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "83099fa6" /\ chksum(tla) = "9c0ebe02")
VARIABLES i, j, output, inSecondInput, pc

vars == << i, j, output, inSecondInput, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ j = 1
        /\ output = << >>
        /\ inSecondInput = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i <= Len(input1)
               THEN /\ j' = i
                    /\ inSecondInput' = FALSE
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(\A x \in 1..Len(input2): ~(\E y \in 1..Len(input1): input1[y] = input2[x]), 
                              "Failure of assertion at line 37, column 13.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << j, inSecondInput >>
         /\ UNCHANGED << i, output >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF j <= Len(input2)
               THEN /\ IF input1[i] = input2[j]
                          THEN /\ inSecondInput' = TRUE
                               /\ j' = Len(input2) + 1
                          ELSE /\ TRUE
                               /\ UNCHANGED << j, inSecondInput >>
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << i, output >>
               ELSE /\ IF inSecondInput = FALSE
                          THEN /\ output' = output \o <<input1[i]>>
                          ELSE /\ TRUE
                               /\ UNCHANGED output
                    /\ i' = i + 1
                    /\ pc' = "Lbl_1"
                    /\ UNCHANGED << j, inSecondInput >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ j' = j + 1
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << i, output, inSecondInput >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Mar 06 17:19:00 EST 2023 by chiddy00
\* Created Mon Mar 06 17:07:11 EST 2023 by chiddy00
