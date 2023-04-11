-------------------- MODULE Lab2_Example_1_Find_2nd_Max --------------------

EXTENDS Integers, Sequences, TLC
(*
    --algorithm get2ndMax {
        variable 
            x \in {23, 46, 69, 109},
            y \in {-23, 34, 56, 77},
            z \in {0, 33, 59},
            result = x \* just initialize result to something
            ;
        
        
        \* main method
        {
            if(x > y /\ x > z) {
                if(y > z) {
                    result := y;
                }
                else {
                    result := z;
                }
            }
            else if(y > z /\ y > x) {
                if(z > x) {
                    result := z;
                }
                else {
                    result := x;
                }
            }
            else { \* z is the biggest
                if(x > y) {
                    result := x;
                }
                else {
                    result := y;
                }
            };
            
            assert
                \/ (/\ x >= result
                    /\ result = y
                    /\ result >= z)
                \/ (/\ x >= result
                    /\ result = z
                    /\ result >= y)
                \/ (/\ y >= result
                    /\ result = x
                    /\ result >= z)
                \/ (/\ y >= result
                    /\ result = z
                    /\ result >= x)
                \/ (/\ z >= result
                    /\ result = x
                    /\ result >= y)
                \/ (/\ z >= result
                    /\ result = y
                    /\ result >= x);
        }
            
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "15888f9" /\ chksum(tla) = "e8d4a5fa")
VARIABLES x, y, z, result, pc

vars == << x, y, z, result, pc >>

Init == (* Global variables *)
        /\ x \in {23, 46, 69, 109}
        /\ y \in {-23, 34, 56, 77}
        /\ z \in {0, 33, 59}
        /\ result = x
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x > y /\ x > z
               THEN /\ IF y > z
                          THEN /\ result' = y
                          ELSE /\ result' = z
               ELSE /\ IF y > z /\ y > x
                          THEN /\ IF z > x
                                     THEN /\ result' = z
                                     ELSE /\ result' = x
                          ELSE /\ IF x > y
                                     THEN /\ result' = x
                                     ELSE /\ result' = y
         /\ Assert(\/ (/\ x >= result'
                       /\ result' = y
                       /\ result' >= z)
                   \/ (/\ x >= result'
                       /\ result' = z
                       /\ result' >= y)
                   \/ (/\ y >= result'
                       /\ result' = x
                       /\ result' >= z)
                   \/ (/\ y >= result'
                       /\ result' = z
                       /\ result' >= x)
                   \/ (/\ z >= result'
                       /\ result' = x
                       /\ result' >= y)
                   \/ (/\ z >= result'
                       /\ result' = y
                       /\ result' >= x), 
                   "Failure of assertion at line 41, column 13.")
         /\ pc' = "Done"
         /\ UNCHANGED << x, y, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Mar 03 22:15:35 EST 2023 by chiddy00
\* Created Fri Mar 03 20:50:35 EST 2023 by chiddy00
