-------------------------- MODULE getRightShifts2 --------------------------

EXTENDS Integers, Sequences, TLC
CONSTANT input, n

(*

    --algorithm getRightShifts2 {
        variable result = input, i = 1, newPos = 0;
        
        \* algorithm
        {
            \*Do Preconditions
            assertNGreater0: assert n > 0;
            assertLenGreater0: assert Len(input) > 0;
            
            whileloop: while(i <= Len(input)) {
                
                calNewPos: newPos := (((i - 1) + n) % Len(input)) + 1;
                
                assignResult: result[newPos] := input[i];
            
                incrementI: i := i + 1;
            };
            
            
            
            assert \A x \in 1..Len(input): input[x] = result[(((x - 1) + n) % Len(input)) + 1];
        }
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "9d34bfc4" /\ chksum(tla) = "e88e196e")
VARIABLES result, i, newPos, pc

vars == << result, i, newPos, pc >>

Init == (* Global variables *)
        /\ result = input
        /\ i = 1
        /\ newPos = 0
        /\ pc = "assertNGreater0"

assertNGreater0 == /\ pc = "assertNGreater0"
                   /\ Assert(n > 0, 
                             "Failure of assertion at line 14, column 30.")
                   /\ pc' = "assertLenGreater0"
                   /\ UNCHANGED << result, i, newPos >>

assertLenGreater0 == /\ pc = "assertLenGreater0"
                     /\ Assert(Len(input) > 0, 
                               "Failure of assertion at line 15, column 32.")
                     /\ pc' = "whileloop"
                     /\ UNCHANGED << result, i, newPos >>

whileloop == /\ pc = "whileloop"
             /\ IF i <= Len(input)
                   THEN /\ pc' = "calNewPos"
                   ELSE /\ Assert(\A x \in 1..Len(input): input[x] = result[(((x - 1) + n) % Len(input)) + 1], 
                                  "Failure of assertion at line 28, column 13.")
                        /\ pc' = "Done"
             /\ UNCHANGED << result, i, newPos >>

calNewPos == /\ pc = "calNewPos"
             /\ newPos' = (((i - 1) + n) % Len(input)) + 1
             /\ pc' = "assignResult"
             /\ UNCHANGED << result, i >>

assignResult == /\ pc = "assignResult"
                /\ result' = [result EXCEPT ![newPos] = input[i]]
                /\ pc' = "incrementI"
                /\ UNCHANGED << i, newPos >>

incrementI == /\ pc = "incrementI"
              /\ i' = i + 1
              /\ pc' = "whileloop"
              /\ UNCHANGED << result, newPos >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == assertNGreater0 \/ assertLenGreater0 \/ whileloop \/ calNewPos
           \/ assignResult \/ incrementI
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Sun Mar 05 21:55:08 EST 2023 by chiddy00
\* Created Sun Mar 05 21:49:02 EST 2023 by chiddy00
