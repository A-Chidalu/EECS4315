------------------------------- MODULE sudoku -------------------------------
EXTENDS Integers, Sequences, TLC, Naturals, FiniteSets

(*
    --algorithm sudoku{
        variable board = <<<<3, 2, 0, 1>>,
                           <<4, 0, 0, 3>>,
                           <<2, 3, 1, 4>>,
                           <<0, 4, 0, 2>>>>,
                 solved = FALSE,
                 row = 1,
                 col = 1,
                 validSet = {1, 2, 3, 4},
                 res = <<>>,
                 res_set = {},
                 i = 1,
                 j = 1,
                 N = 4,
                 SQRT_N = 2,
                 element = 1,
                 board_valid = FALSE;
        
        
        procedure isSolved() {
            
            call isValid();
            
            i := 1;
            j := 1;
            
            
            while(i <= N){
                
                while(j <= N){
                    if(board[i][j] = 0){
                        solved := FALSE;
                    };
                    j := j + 1;
                };
            
                i := i + 1;
            };
            
            solved := solved /\ board_valid;
        
        }
                 
                

        procedure isValid() {
            res := <<>>;
            res_set := {};
            board_valid := FALSE;
            
            i := 1;
            j := 1;
            
            
            while(i <= N){
                
                while(j <= N){
                    element := board[i][j];
                    if(element # 0){
                        res := res \o <<i, element>>;
                        res := res \o <<element, j>>;
                        res := res \o <<i \div SQRT_N, j \div SQRT_N, element>>;
                        
                        res_set := res_set \cup {<<i, element>>};
                        res_set := res_set \cup {<<element, j>>};
                        res_set := res_set \cup {<<i \div SQRT_N, j \div SQRT_N, element>>};
                    };
                    
                    j := j + 1;
                };
            
                i := i + 1;
            };
            
            if(Len(res) = Cardinality(res_set)){
               board_valid := TRUE;
            };
            return;
        }
        \*Main Method
        {
            
            
            call isValid();
            
            assert board_valid = TRUE;
        
        }
    
    
    
    }

    

*)
\* BEGIN TRANSLATION (chksum(pcal) = "5af9d0bb" /\ chksum(tla) = "7c7a5af1")
VARIABLES board, solved, row, col, validSet, res, res_set, i, j, N, SQRT_N, 
          element, board_valid, pc, stack

vars == << board, solved, row, col, validSet, res, res_set, i, j, N, SQRT_N, 
           element, board_valid, pc, stack >>

Init == (* Global variables *)
        /\ board = <<<<3, 2, 0, 1>>,
                     <<4, 0, 0, 3>>,
                     <<2, 3, 1, 4>>,
                     <<0, 4, 0, 2>>>>
        /\ solved = FALSE
        /\ row = 1
        /\ col = 1
        /\ validSet = {1, 2, 3, 4}
        /\ res = <<>>
        /\ res_set = {}
        /\ i = 1
        /\ j = 1
        /\ N = 4
        /\ SQRT_N = 2
        /\ element = 1
        /\ board_valid = FALSE
        /\ stack = << >>
        /\ pc = "Lbl_13"

Lbl_1 == /\ pc = "Lbl_1"
         /\ stack' = << [ procedure |->  "isValid",
                          pc        |->  "Lbl_2" ] >>
                      \o stack
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << board, solved, row, col, validSet, res, res_set, i, j, 
                         N, SQRT_N, element, board_valid >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ i' = 1
         /\ j' = 1
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << board, solved, row, col, validSet, res, res_set, N, 
                         SQRT_N, element, board_valid, stack >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF i <= N
               THEN /\ pc' = "Lbl_4"
                    /\ UNCHANGED solved
               ELSE /\ solved' = (solved /\ board_valid)
                    /\ pc' = "Error"
         /\ UNCHANGED << board, row, col, validSet, res, res_set, i, j, N, 
                         SQRT_N, element, board_valid, stack >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ IF j <= N
               THEN /\ IF board[i][j] = 0
                          THEN /\ solved' = FALSE
                          ELSE /\ TRUE
                               /\ UNCHANGED solved
                    /\ j' = j + 1
                    /\ pc' = "Lbl_4"
                    /\ i' = i
               ELSE /\ i' = i + 1
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << solved, j >>
         /\ UNCHANGED << board, row, col, validSet, res, res_set, N, SQRT_N, 
                         element, board_valid, stack >>

isSolved == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4

Lbl_5 == /\ pc = "Lbl_5"
         /\ res' = <<>>
         /\ res_set' = {}
         /\ board_valid' = FALSE
         /\ i' = 1
         /\ j' = 1
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << board, solved, row, col, validSet, N, SQRT_N, element, 
                         stack >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ IF i <= N
               THEN /\ pc' = "Lbl_7"
                    /\ UNCHANGED << board_valid, stack >>
               ELSE /\ IF Len(res) = Cardinality(res_set)
                          THEN /\ board_valid' = TRUE
                          ELSE /\ TRUE
                               /\ UNCHANGED board_valid
                    /\ pc' = Head(stack).pc
                    /\ stack' = Tail(stack)
         /\ UNCHANGED << board, solved, row, col, validSet, res, res_set, i, j, 
                         N, SQRT_N, element >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ IF j <= N
               THEN /\ element' = board[i][j]
                    /\ IF element' # 0
                          THEN /\ res' = res \o <<i, element'>>
                               /\ pc' = "Lbl_8"
                          ELSE /\ pc' = "Lbl_12"
                               /\ res' = res
                    /\ i' = i
               ELSE /\ i' = i + 1
                    /\ pc' = "Lbl_6"
                    /\ UNCHANGED << res, element >>
         /\ UNCHANGED << board, solved, row, col, validSet, res_set, j, N, 
                         SQRT_N, board_valid, stack >>

Lbl_12 == /\ pc = "Lbl_12"
          /\ j' = j + 1
          /\ pc' = "Lbl_7"
          /\ UNCHANGED << board, solved, row, col, validSet, res, res_set, i, 
                          N, SQRT_N, element, board_valid, stack >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ res' = res \o <<element, j>>
         /\ pc' = "Lbl_9"
         /\ UNCHANGED << board, solved, row, col, validSet, res_set, i, j, N, 
                         SQRT_N, element, board_valid, stack >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ res' = res \o <<i \div SQRT_N, j \div SQRT_N, element>>
         /\ res_set' = (res_set \cup {<<i, element>>})
         /\ pc' = "Lbl_10"
         /\ UNCHANGED << board, solved, row, col, validSet, i, j, N, SQRT_N, 
                         element, board_valid, stack >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ res_set' = (res_set \cup {<<element, j>>})
          /\ pc' = "Lbl_11"
          /\ UNCHANGED << board, solved, row, col, validSet, res, i, j, N, 
                          SQRT_N, element, board_valid, stack >>

Lbl_11 == /\ pc = "Lbl_11"
          /\ res_set' = (res_set \cup {<<i \div SQRT_N, j \div SQRT_N, element>>})
          /\ pc' = "Lbl_12"
          /\ UNCHANGED << board, solved, row, col, validSet, res, i, j, N, 
                          SQRT_N, element, board_valid, stack >>

isValid == Lbl_5 \/ Lbl_6 \/ Lbl_7 \/ Lbl_12 \/ Lbl_8 \/ Lbl_9 \/ Lbl_10
              \/ Lbl_11

Lbl_13 == /\ pc = "Lbl_13"
          /\ stack' = << [ procedure |->  "isValid",
                           pc        |->  "Lbl_14" ] >>
                       \o stack
          /\ pc' = "Lbl_5"
          /\ UNCHANGED << board, solved, row, col, validSet, res, res_set, i, 
                          j, N, SQRT_N, element, board_valid >>

Lbl_14 == /\ pc = "Lbl_14"
          /\ Assert(board_valid = TRUE, 
                    "Failure of assertion at line 90, column 13.")
          /\ pc' = "Done"
          /\ UNCHANGED << board, solved, row, col, validSet, res, res_set, i, 
                          j, N, SQRT_N, element, board_valid, stack >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == isSolved \/ isValid \/ Lbl_13 \/ Lbl_14
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Apr 10 23:06:47 EDT 2023 by chiddy00
\* Created Mon Apr 10 22:19:41 EDT 2023 by chiddy00
