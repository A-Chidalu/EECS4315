---------------------------- MODULE binarySearch ----------------------------
EXTENDS Integers, Sequences, TLC, Reals
CONSTANTS input, target




(*
    --algorithm binarySearch { \*open algorithm
        variables lo = 1, hi = Len(input), mid = 1, result = -1;
        
        
        
        
        {
            precond1: assert Len(input) > 0;
            
            precond2: assert Len(input) > 1 => (\A x \in 2..Len(input): input[x] >= input[x - 1]);
            
            openWhile: while(lo <= hi) {
                calMid: mid := lo + (hi - lo) / 2;
                
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
            
            
            
            postCond1: assert result > 0 => input[result] = target;
            
            
        }
    } \*close algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "33072fc2" /\ chksum(tla) = "3b94a400")
VARIABLES lo, hi, mid, result, pc

vars == << lo, hi, mid, result, pc >>

Init == (* Global variables *)
        /\ lo = 1
        /\ hi = Len(input)
        /\ mid = 1
        /\ result = -1
        /\ pc = "precond1"

precond1 == /\ pc = "precond1"
            /\ Assert(Len(input) > 0, 
                      "Failure of assertion at line 16, column 23.")
            /\ pc' = "precond2"
            /\ UNCHANGED << lo, hi, mid, result >>

precond2 == /\ pc = "precond2"
            /\ Assert(Len(input) > 1 => (\A x \in 2..Len(input): input[x] >= input[x - 1]), 
                      "Failure of assertion at line 18, column 23.")
            /\ pc' = "openWhile"
            /\ UNCHANGED << lo, hi, mid, result >>

openWhile == /\ pc = "openWhile"
             /\ IF lo <= hi
                   THEN /\ pc' = "calMid"
                   ELSE /\ pc' = "postCond1"
             /\ UNCHANGED << lo, hi, mid, result >>

calMid == /\ pc = "calMid"
          /\ mid' = lo + (hi - lo) / 2
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
          /\ pc' = "openWhile"

postCond1 == /\ pc = "postCond1"
             /\ Assert(result > 0 => input[result] = target, 
                       "Failure of assertion at line 37, column 24.")
             /\ pc' = "Done"
             /\ UNCHANGED << lo, hi, mid, result >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == precond1 \/ precond2 \/ openWhile \/ calMid \/ postCond1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Mon Mar 06 11:46:52 EST 2023 by chiddy00
\* Created Mon Mar 06 11:19:51 EST 2023 by chiddy00
