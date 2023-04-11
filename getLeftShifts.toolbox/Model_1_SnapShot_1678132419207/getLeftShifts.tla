--------------------------- MODULE getLeftShifts ---------------------------

EXTENDS Integers, Sequences, TLC
CONSTANT input, n

(*
    --algorithm getLeftShifts {
        variable 
            normalizeN = ((n - 1) % Len(input)) + 1, 
            i = 1,
            result = input,
            newPos = 0;
        
        \* main method
        {
            
            
           beginWhile: while(i <= Len(input)) {
                
                calNewPos: newPos := (((i - 1) - normalizeN + Len(input)) % Len(input)) + 1;
                assignResult: result[newPos] := input[i];
                
              
                incrementI: i := i + 1;
           };
           
           
            doAssertion: assert \A x \in 1..Len(input): input[x] = result[(((x - 1) - normalizeN + Len(input)) % Len(input)) + 1];
        }
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "75e745b0" /\ chksum(tla) = "2d864dce")
VARIABLES normalizeN, i, result, newPos, pc

vars == << normalizeN, i, result, newPos, pc >>

Init == (* Global variables *)
        /\ normalizeN = ((n - 1) % Len(input)) + 1
        /\ i = 1
        /\ result = input
        /\ newPos = 0
        /\ pc = "beginWhile"

beginWhile == /\ pc = "beginWhile"
              /\ IF i <= Len(input)
                    THEN /\ pc' = "calNewPos"
                    ELSE /\ pc' = "doAssertion"
              /\ UNCHANGED << normalizeN, i, result, newPos >>

calNewPos == /\ pc = "calNewPos"
             /\ newPos' = (((i - 1) - normalizeN + Len(input)) % Len(input)) + 1
             /\ pc' = "assignResult"
             /\ UNCHANGED << normalizeN, i, result >>

assignResult == /\ pc = "assignResult"
                /\ result' = [result EXCEPT ![newPos] = input[i]]
                /\ pc' = "incrementI"
                /\ UNCHANGED << normalizeN, i, newPos >>

incrementI == /\ pc = "incrementI"
              /\ i' = i + 1
              /\ pc' = "beginWhile"
              /\ UNCHANGED << normalizeN, result, newPos >>

doAssertion == /\ pc = "doAssertion"
               /\ Assert(\A x \in 1..Len(input): input[x] = result[(((x - 1) - normalizeN + Len(input)) % Len(input)) + 1], 
                         "Failure of assertion at line 28, column 26.")
               /\ pc' = "Done"
               /\ UNCHANGED << normalizeN, i, result, newPos >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == beginWhile \/ calNewPos \/ assignResult \/ incrementI
           \/ doAssertion
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Mar 06 14:53:27 EST 2023 by chiddy00
\* Created Mon Mar 06 13:59:02 EST 2023 by chiddy00
