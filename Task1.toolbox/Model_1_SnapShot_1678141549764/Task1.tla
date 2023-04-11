------------------------------- MODULE Task1 -------------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT input1, input2

(*
    --algorithm Task1{
        variable i = 1, j = 1, output = << >>, inSecondInput = FALSE;
        
        {
            
            
            loopOverI: while(i <= Len(input1)) {
                
                
                assignJToI: j := 1;
                resetInSecondInput: inSecondInput := FALSE;
                loopOverInputj: while(j <= Len(input2)){
                    checkIfInput1AtIEqualsInput2AtJ: if(input1[i] = input2[j]) {
                        setInSecondInputTrue: inSecondInput := TRUE;
                        break: j := Len(input2) + 1;
                    };
                    
                    incrementJ: j := j + 1;
                };
                
                
                checkInSecondInputIsFalse: if(inSecondInput = FALSE) {
                    AddToOutput: output := output \o <<input1[i]>>;
                };
                
                
                
                incrementI: i := i + 1;
            };
            
            
            postCondition: assert \A x \in 1..Len(input2): ~(\E y \in 1..Len(input1): input1[y] = input2[x]);
            
            
        }
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "6623c981" /\ chksum(tla) = "22e85330")
VARIABLES i, j, output, inSecondInput, pc

vars == << i, j, output, inSecondInput, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ j = 1
        /\ output = << >>
        /\ inSecondInput = FALSE
        /\ pc = "loopOverI"

loopOverI == /\ pc = "loopOverI"
             /\ IF i <= Len(input1)
                   THEN /\ pc' = "assignJToI"
                   ELSE /\ pc' = "postCondition"
             /\ UNCHANGED << i, j, output, inSecondInput >>

assignJToI == /\ pc = "assignJToI"
              /\ j' = 1
              /\ pc' = "resetInSecondInput"
              /\ UNCHANGED << i, output, inSecondInput >>

resetInSecondInput == /\ pc = "resetInSecondInput"
                      /\ inSecondInput' = FALSE
                      /\ pc' = "loopOverInputj"
                      /\ UNCHANGED << i, j, output >>

loopOverInputj == /\ pc = "loopOverInputj"
                  /\ IF j <= Len(input2)
                        THEN /\ pc' = "checkIfInput1AtIEqualsInput2AtJ"
                        ELSE /\ pc' = "checkInSecondInputIsFalse"
                  /\ UNCHANGED << i, j, output, inSecondInput >>

checkIfInput1AtIEqualsInput2AtJ == /\ pc = "checkIfInput1AtIEqualsInput2AtJ"
                                   /\ IF input1[i] = input2[j]
                                         THEN /\ pc' = "setInSecondInputTrue"
                                         ELSE /\ pc' = "incrementJ"
                                   /\ UNCHANGED << i, j, output, inSecondInput >>

setInSecondInputTrue == /\ pc = "setInSecondInputTrue"
                        /\ inSecondInput' = TRUE
                        /\ pc' = "break"
                        /\ UNCHANGED << i, j, output >>

break == /\ pc = "break"
         /\ j' = Len(input2) + 1
         /\ pc' = "incrementJ"
         /\ UNCHANGED << i, output, inSecondInput >>

incrementJ == /\ pc = "incrementJ"
              /\ j' = j + 1
              /\ pc' = "loopOverInputj"
              /\ UNCHANGED << i, output, inSecondInput >>

checkInSecondInputIsFalse == /\ pc = "checkInSecondInputIsFalse"
                             /\ IF inSecondInput = FALSE
                                   THEN /\ pc' = "AddToOutput"
                                   ELSE /\ pc' = "incrementI"
                             /\ UNCHANGED << i, j, output, inSecondInput >>

AddToOutput == /\ pc = "AddToOutput"
               /\ output' = output \o <<input1[i]>>
               /\ pc' = "incrementI"
               /\ UNCHANGED << i, j, inSecondInput >>

incrementI == /\ pc = "incrementI"
              /\ i' = i + 1
              /\ pc' = "loopOverI"
              /\ UNCHANGED << j, output, inSecondInput >>

postCondition == /\ pc = "postCondition"
                 /\ Assert(\A x \in 1..Len(input2): ~(\E y \in 1..Len(input1): input1[y] = input2[x]), 
                           "Failure of assertion at line 37, column 28.")
                 /\ pc' = "Done"
                 /\ UNCHANGED << i, j, output, inSecondInput >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == loopOverI \/ assignJToI \/ resetInSecondInput \/ loopOverInputj
           \/ checkIfInput1AtIEqualsInput2AtJ \/ setInSecondInputTrue \/ break
           \/ incrementJ \/ checkInSecondInputIsFalse \/ AddToOutput
           \/ incrementI \/ postCondition
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Mar 06 17:25:43 EST 2023 by chiddy00
\* Created Mon Mar 06 17:07:11 EST 2023 by chiddy00
