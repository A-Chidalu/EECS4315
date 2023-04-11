------------------------ MODULE decideRPSGameResult ------------------------
EXTENDS Integers, Sequences, TLC

(*
    --algorithm decideRPSGameResult {
        variables 
            p1r1 \in {"R", "P", "S"},
            p1r2 \in {"R", "P", "S"},
            p2r1 \in {"R", "P", "S"},
            p2r2 \in {"R", "P", "S"},
            numRoundsWonByPlayer1 = 0,
            numRoundsWonByPlayer2 = 0,
            p1win = FALSE,
            p2win = FALSE,
            tie = FALSE;
        
        \* main method
        {
            \* round1
            if(p1r1 = "R" /\ p2r1 = "R") {
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r1 = "R" /\ p2r1 = "P") {
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r1 = "R" /\ p2r1 = "S") {
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
            }
            else if(p1r1 = "P" /\ p2r1 = "R") {
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
            }
            else if(p1r1 = "P" /\ p2r1 = "P") {
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r1 = "P" /\ p2r1 = "S") {
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r1 = "S" /\ p2r1 = "R") {
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r1 = "S" /\ p2r1 = "P") {
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else { \* S S 
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            };
            
            \* round2
            if(p1r2 = "R" /\ p2r2 = "R") {
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r2 = "R" /\ p2r2 = "P") {
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r2 = "R" /\ p2r2 = "S") {
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
            }
            else if(p1r2 = "P" /\ p2r2 = "R") {
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
            }
            else if(p1r2 = "P" /\ p2r2 = "P") {
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r2 = "P" /\ p2r2 = "S") {
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r2 = "S" /\ p2r2 = "R") {
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else if(p1r2 = "S" /\ p2r2 = "P") {
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            }
            else { \* S S 
                numRoundsWonByPlayer1 := numRoundsWonByPlayer1 + 1;
                numRoundsWonByPlayer2 := numRoundsWonByPlayer2 + 1;
            };
            
            
            
            if(numRoundsWonByPlayer1 > numRoundsWonByPlayer2) {
                p1win := TRUE;            
            }
            else if(numRoundsWonByPlayer2 > numRoundsWonByPlayer1) {
                p2win := TRUE;
            }
            else {
                tie := TRUE;
            };
            
            
            assert (p1win /\ ~p2win /\ ~tie) \/ (~p1win /\ p2win /\ ~tie) \/ (~p1win /\ ~p2win /\ tie);
        }
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3b93d23a" /\ chksum(tla) = "61da908f")
VARIABLES p1r1, p1r2, p2r1, p2r2, numRoundsWonByPlayer1, 
          numRoundsWonByPlayer2, p1win, p2win, tie, pc

vars == << p1r1, p1r2, p2r1, p2r2, numRoundsWonByPlayer1, 
           numRoundsWonByPlayer2, p1win, p2win, tie, pc >>

Init == (* Global variables *)
        /\ p1r1 \in {"R", "P", "S"}
        /\ p1r2 \in {"R", "P", "S"}
        /\ p2r1 \in {"R", "P", "S"}
        /\ p2r2 \in {"R", "P", "S"}
        /\ numRoundsWonByPlayer1 = 0
        /\ numRoundsWonByPlayer2 = 0
        /\ p1win = FALSE
        /\ p2win = FALSE
        /\ tie = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF p1r1 = "R" /\ p2r1 = "R"
               THEN /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
                    /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
               ELSE /\ IF p1r1 = "R" /\ p2r1 = "P"
                          THEN /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
                               /\ UNCHANGED numRoundsWonByPlayer1
                          ELSE /\ IF p1r1 = "R" /\ p2r1 = "S"
                                     THEN /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
                                          /\ UNCHANGED numRoundsWonByPlayer2
                                     ELSE /\ IF p1r1 = "P" /\ p2r1 = "R"
                                                THEN /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
                                                     /\ UNCHANGED numRoundsWonByPlayer2
                                                ELSE /\ IF p1r1 = "P" /\ p2r1 = "P"
                                                           THEN /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
                                                                /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
                                                           ELSE /\ IF p1r1 = "P" /\ p2r1 = "S"
                                                                      THEN /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
                                                                           /\ UNCHANGED numRoundsWonByPlayer1
                                                                      ELSE /\ IF p1r1 = "S" /\ p2r1 = "R"
                                                                                 THEN /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
                                                                                      /\ UNCHANGED numRoundsWonByPlayer1
                                                                                 ELSE /\ IF p1r1 = "S" /\ p2r1 = "P"
                                                                                            THEN /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
                                                                                                 /\ UNCHANGED numRoundsWonByPlayer1
                                                                                            ELSE /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
                                                                                                 /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
         /\ IF p1r2 = "R" /\ p2r2 = "R"
               THEN /\ pc' = "Lbl_2"
               ELSE /\ IF p1r2 = "R" /\ p2r2 = "P"
                          THEN /\ pc' = "Lbl_3"
                          ELSE /\ IF p1r2 = "R" /\ p2r2 = "S"
                                     THEN /\ pc' = "Lbl_4"
                                     ELSE /\ IF p1r2 = "P" /\ p2r2 = "R"
                                                THEN /\ pc' = "Lbl_5"
                                                ELSE /\ IF p1r2 = "P" /\ p2r2 = "P"
                                                           THEN /\ pc' = "Lbl_6"
                                                           ELSE /\ IF p1r2 = "P" /\ p2r2 = "S"
                                                                      THEN /\ pc' = "Lbl_7"
                                                                      ELSE /\ IF p1r2 = "S" /\ p2r2 = "R"
                                                                                 THEN /\ pc' = "Lbl_8"
                                                                                 ELSE /\ IF p1r2 = "S" /\ p2r2 = "P"
                                                                                            THEN /\ pc' = "Lbl_9"
                                                                                            ELSE /\ pc' = "Lbl_10"
         /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, p1win, p2win, tie >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
         /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, p1win, p2win, tie >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, numRoundsWonByPlayer1, p1win, 
                         p2win, tie >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, numRoundsWonByPlayer2, p1win, 
                         p2win, tie >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, numRoundsWonByPlayer2, p1win, 
                         p2win, tie >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
         /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, p1win, p2win, tie >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, numRoundsWonByPlayer1, p1win, 
                         p2win, tie >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, numRoundsWonByPlayer1, p1win, 
                         p2win, tie >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, numRoundsWonByPlayer1, p1win, 
                         p2win, tie >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ numRoundsWonByPlayer1' = numRoundsWonByPlayer1 + 1
          /\ numRoundsWonByPlayer2' = numRoundsWonByPlayer2 + 1
          /\ pc' = "Lbl_11"
          /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, p1win, p2win, tie >>

Lbl_11 == /\ pc = "Lbl_11"
          /\ IF numRoundsWonByPlayer1 > numRoundsWonByPlayer2
                THEN /\ p1win' = TRUE
                     /\ UNCHANGED << p2win, tie >>
                ELSE /\ IF numRoundsWonByPlayer2 > numRoundsWonByPlayer1
                           THEN /\ p2win' = TRUE
                                /\ tie' = tie
                           ELSE /\ tie' = TRUE
                                /\ p2win' = p2win
                     /\ p1win' = p1win
          /\ Assert((p1win' /\ ~p2win' /\ ~tie') \/ (~p1win' /\ p2win' /\ ~tie') \/ (~p1win' /\ ~p2win' /\ tie'), 
                    "Failure of assertion at line 96, column 13.")
          /\ pc' = "Done"
          /\ UNCHANGED << p1r1, p1r2, p2r1, p2r2, numRoundsWonByPlayer1, 
                          numRoundsWonByPlayer2 >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7
           \/ Lbl_8 \/ Lbl_9 \/ Lbl_10 \/ Lbl_11
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Sun Mar 05 00:26:13 EST 2023 by chiddy00
\* Created Fri Mar 03 22:32:20 EST 2023 by chiddy00
