---------------------------- MODULE binarySearch ----------------------------
EXTENDS Integers, Sequences, TLC, Reals
CONSTANTS input, target




(*
    --algorithm binarySearch { \*open algorithm
        variables lo = 1, hi = Len(input), mid = 1, result = -1;
        
        
        
        
        {
            assert Len(input) > 0;
            
            assert Len(input) > 1 => (\A x \in 2..Len(input): input[x] >= input[x - 1]);
            
            while(lo <= hi) {
                mid := lo + (hi - lo) / 2;
                
                if(input[mid] = target) {
                    result := mid;
                    lo := hi + 1;
                }
                else if(input[mid] > target) {
                    hi := mid - 1;
                }
                else {
                    lo := mid + 1;
                };
            };
            
            
            
            assert result > 0 => input[result] = target;
            
            
        }
    } \*close algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "fe378b28" /\ chksum(tla) = "c725ddf0")
VARIABLES lo, hi, mid, result, pc

vars == << lo, hi, mid, result, pc >>

Init == (* Global variables *)
        /\ lo = 1
        /\ hi = Len(input)
        /\ mid = 1
        /\ result = -1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Len(input) > 0, 
                   "Failure of assertion at line 16, column 13.")
         /\ Assert(Len(input) > 1 => (\A x \in 2..Len(input): input[x] >= input[x - 1]), 
                   "Failure of assertion at line 18, column 13.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << lo, hi, mid, result >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF lo <= hi
               THEN /\ mid' = lo + (hi - lo) / 2
                    /\ IF input[mid'] = target
                          THEN /\ result' = mid'
                               /\ lo' = hi + 1
                               /\ hi' = hi
                          ELSE /\ IF input[mid'] > target
                                     THEN /\ hi' = mid' - 1
                                          /\ lo' = lo
                                     ELSE /\ lo' = mid' + 1
                                          /\ hi' = hi
                               /\ UNCHANGED result
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(result > 0 => input[result] = target, 
                              "Failure of assertion at line 37, column 13.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << lo, hi, mid, result >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Mon Mar 06 11:34:05 EST 2023 by chiddy00
\* Created Mon Mar 06 11:19:51 EST 2023 by chiddy00
