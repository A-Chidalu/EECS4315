------------------------ MODULE sameNumThreeAndFour ------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT input





(*
    --algorithm sameNumThreeAndFour {
        
        
        \* main method
        {
            \* Preconditions: Array contains same number of three and 4
            assert Cardinality({x \in input : x = 3}) = Cardinality({x \in input : x = 4});
            assert (\A x \in 1..Len(input): 
                (x # Len(input) /\ input[x] = 3 => input[x + 1] # 3)
                );
                
           
           
           
            
            
        }
    }

*)
\* BEGIN TRANSLATION (chksum(pcal) = "afd390f2" /\ chksum(tla) = "6031f963")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Cardinality({x \in input : x = 3}) = Cardinality({x \in input : x = 4}), 
                   "Failure of assertion at line 16, column 13.")
         /\ Assert(   (\A x \in 1..Len(input):
                   (x # Len(input) /\ input[x] = 3 => input[x + 1] # 3)
                   ), "Failure of assertion at line 17, column 13.")
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Mar 06 22:15:36 EST 2023 by chiddy00
\* Created Mon Mar 06 21:46:10 EST 2023 by chiddy00
