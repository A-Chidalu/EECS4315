----------------------------- MODULE isAnagram -----------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT input1, input2

(*
    --algorithm isAnagram{
        variable i = 1, j = 1, output = TRUE, found = FALSE;
        
        \* main method
        {
        
            if(Len(input1) = Len(input2)){
                  
                 while(i <= Len(input1)){
                    
                    found := FALSE;
                    \* want to make sure that for each element in input1, I can find it in input2
                    while(j <= Len(input2)) {
                        
                        if(input2[j] = input1[i]){
                            print("Found what im looking for!");
                            found := TRUE;
                        };
                        
                        j := j + 1;
                    };
                    
                    
                    if(found # TRUE){
                        print("IM in here!");
                        output := FALSE;
                    };
                    
                    
                    i := i + 1;
                    
                 };   
                
            }
            else {
                
                output := FALSE;
                
            };
            
            
            assert output = TRUE <=> Len(input1) = Len(input2) /\ (\A x \in 1..Len(input1): (\E y \in 1..Len(input2): input1[x] = input2[y]))
        
        }
    
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "ff0fd443" /\ chksum(tla) = "7cd8fb10")
VARIABLES i, j, output, found, pc

vars == << i, j, output, found, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ j = 1
        /\ output = TRUE
        /\ found = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(input1) = Len(input2)
               THEN /\ pc' = "Lbl_2"
                    /\ UNCHANGED output
               ELSE /\ output' = FALSE
                    /\ pc' = "Lbl_4"
         /\ UNCHANGED << i, j, found >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i <= Len(input1)
               THEN /\ found' = FALSE
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Lbl_4"
                    /\ found' = found
         /\ UNCHANGED << i, j, output >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF j <= Len(input2)
               THEN /\ IF input2[j] = input1[i]
                          THEN /\ PrintT(("Found what im looking for!"))
                               /\ found' = TRUE
                          ELSE /\ TRUE
                               /\ found' = found
                    /\ j' = j + 1
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << i, output >>
               ELSE /\ IF found # TRUE
                          THEN /\ PrintT(("IM in here!"))
                               /\ output' = FALSE
                          ELSE /\ TRUE
                               /\ UNCHANGED output
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED << j, found >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ Assert(output = TRUE <=> Len(input1) = Len(input2) /\ (\A x \in 1..Len(input1): (\E y \in 1..Len(input2): input1[x] = input2[y])), 
                   "Failure of assertion at line 47, column 13.")
         /\ pc' = "Done"
         /\ UNCHANGED << i, j, output, found >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Apr 03 20:44:18 EDT 2023 by chiddy00
\* Created Sun Apr 02 17:48:02 EDT 2023 by chiddy00
