\* THis module will check if input1 is a subarray of input2
----------------------------- MODULE isSubarray -----------------------------

EXTENDS Integers, Sequences, TLC
CONSTANT input1, input2

(*

    --algorithm isSubarray {
        variable output = FALSE, 
                 i = 1, 
                 j = 1, 
                 k = 0, 
                 allEqual = FALSE;
        
    
    }
*)

=============================================================================
\* Modification History
\* Last modified Sun Apr 02 17:01:00 EDT 2023 by chiddy00
\* Created Sun Apr 02 16:20:28 EDT 2023 by chiddy00
