------------------------ MODULE decideRPSGameResult ------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT input


(*
--algorithm FindMax {
    variables result = input[1], i = 1;
    {
        \* precondition
        assert Len(input) > 0;
        
        while (i <= Len(input)) {
            if(input[i] > result) {
                result := input[i];
            };
            i := i + 1;
        };
        
        \* postconditions
        assert \A j \in 1..Len(input): result >= input[j];
    }
} 
*)
\* BEGIN TRANSLATION (chksum(pcal) = "2cd2317b" /\ chksum(tla) = "82d5b1fe")
VARIABLES result, i, pc

vars == << result, i, pc >>

Init == (* Global variables *)
        /\ result = input[1]
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Len(input) > 0, 
                   "Failure of assertion at line 11, column 9.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << result, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i <= Len(input)
               THEN /\ IF input[i] > result
                          THEN /\ result' = input[i]
                          ELSE /\ TRUE
                               /\ UNCHANGED result
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(\A j \in 1..Len(input): result >= input[j], 
                              "Failure of assertion at line 21, column 9.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << result, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Fri Mar 03 22:59:39 EST 2023 by chiddy00
\* Created Fri Mar 03 22:32:20 EST 2023 by chiddy00
