--------------------------- MODULE getAllSuffixes ---------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT input

(*
    --algorithm getAllSuffixes {
        variable result = input, i = 1, j = 0, dummy = << >>;
        
        
       \* main method
       {
            assert Len(input) > 0;
       
            while(i <= Len(input)) {
                dummy := << >>;
                
                j := i;
                while(j <= Len(input)) {
                    dummy := dummy \o input[j];
                    
                    j := j + 1;
                };
                
                result[i] := dummy;
                
                i := i + 1;
            };
            
            
            \*assert (\A k \in 1..Len(input)): (\A l \in k..Len(input)): <<i>> \in result;
       } 
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "ebbd6c27" /\ chksum(tla) = "64ea910")
VARIABLES result, i, j, dummy, pc

vars == << result, i, j, dummy, pc >>

Init == (* Global variables *)
        /\ result = input
        /\ i = 1
        /\ j = 0
        /\ dummy = << >>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Len(input) > 0, 
                   "Failure of assertion at line 12, column 13.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << result, i, j, dummy >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i <= Len(input)
               THEN /\ dummy' = << >>
                    /\ j' = i
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << j, dummy >>
         /\ UNCHANGED << result, i >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF j <= Len(input)
               THEN /\ dummy' = dummy \o input[j]
                    /\ j' = j + 1
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << result, i >>
               ELSE /\ result' = [result EXCEPT ![i] = dummy]
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED << j, dummy >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Mar 05 19:18:29 EST 2023 by chiddy00
\* Created Sun Mar 05 00:32:17 EST 2023 by chiddy00
