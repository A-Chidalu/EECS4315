------------------------------- MODULE Task2 -------------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT input



(*

--algorithm Task2 {
    variable i = 1, output = << >>, currNum = 0;
    
    
    \* main method
    {
        
        
        while(i <= Len(input)){

            
            currNum := input[i];
            
            if(currNum % 3 = 0){
                output := Append(output, currNum);
            };
        
        
            i := i + 1;
        };
        
        
        
        
    }


}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "ec1a4b53" /\ chksum(tla) = "779f1e15")
VARIABLES i, output, currNum, pc

vars == << i, output, currNum, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ output = << >>
        /\ currNum = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i <= Len(input)
               THEN /\ currNum' = input[i]
                    /\ IF currNum' % 3 = 0
                          THEN /\ output' = Append(output, currNum')
                          ELSE /\ TRUE
                               /\ UNCHANGED output
                    /\ i' = i + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << i, output, currNum >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Mar 06 18:01:02 EST 2023 by chiddy00
\* Created Mon Mar 06 17:43:19 EST 2023 by chiddy00
