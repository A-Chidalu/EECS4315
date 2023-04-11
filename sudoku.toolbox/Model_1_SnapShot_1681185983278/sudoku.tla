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
                 res = << >>,
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
            solved := TRUE;
            
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
            res := << >>;
            res_set := {};
            board_valid := FALSE;
            
            i := 1;
            j := 1;
            
            
            while(i <= N){
                
                while(j <= N){
                    element := board[i][j];
                    if(element # 0){
                        res := res \o << <<i, element>> >>;
                        print(res);
                        res := res \o << <<element, j>> >>;
                        res := res \o << <<i \div SQRT_N, j \div SQRT_N, element>> >>;
                        
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
            
            row := 1;
            col := 1;
            
            while(row <= N){
                
                while(col <= N){
                    if(board[row][col] = 0){
                        board[row][col] := 1;
                        call isValid();
                    };
                    col := col + 1;
                };
            
                row := row + 1;
            };
            
             
        
        }
    
    
    
    }

    

*)
\* BEGIN TRANSLATION (chksum(pcal) = "641342e7" /\ chksum(tla) = "f9cc9c6f")
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
        /\ res = << >>
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
         /\ solved' = TRUE
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << board, row, col, validSet, res, res_set, N, SQRT_N, 
                         element, board_valid, stack >>

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
         /\ res' = << >>
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
                          THEN /\ res' = res \o << <<i, element'>> >>
                               /\ PrintT((res'))
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
         /\ res' = res \o << <<element, j>> >>
         /\ pc' = "Lbl_9"
         /\ UNCHANGED << board, solved, row, col, validSet, res_set, i, j, N, 
                         SQRT_N, element, board_valid, stack >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ res' = res \o << <<i \div SQRT_N, j \div SQRT_N, element>> >>
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
          /\ row' = 1
          /\ col' = 1
          /\ pc' = "Lbl_14"
          /\ UNCHANGED << board, solved, validSet, res, res_set, i, j, N, 
                          SQRT_N, element, board_valid, stack >>

Lbl_14 == /\ pc = "Lbl_14"
          /\ IF row <= N
                THEN /\ pc' = "Lbl_15"
                ELSE /\ pc' = "Done"
          /\ UNCHANGED << board, solved, row, col, validSet, res, res_set, i, 
                          j, N, SQRT_N, element, board_valid, stack >>

Lbl_15 == /\ pc = "Lbl_15"
          /\ IF col <= N
                THEN /\ IF board[row][col] = 0
                           THEN /\ board' = [board EXCEPT ![row][col] = 1]
                                /\ stack' = << [ procedure |->  "isValid",
                                                 pc        |->  "Lbl_16" ] >>
                                             \o stack
                                /\ pc' = "Lbl_5"
                           ELSE /\ pc' = "Lbl_16"
                                /\ UNCHANGED << board, stack >>
                     /\ row' = row
                ELSE /\ row' = row + 1
                     /\ pc' = "Lbl_14"
                     /\ UNCHANGED << board, stack >>
          /\ UNCHANGED << solved, col, validSet, res, res_set, i, j, N, SQRT_N, 
                          element, board_valid >>

Lbl_16 == /\ pc = "Lbl_16"
          /\ col' = col + 1
          /\ pc' = "Lbl_15"
          /\ UNCHANGED << board, solved, row, validSet, res, res_set, i, j, N, 
                          SQRT_N, element, board_valid, stack >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == isSolved \/ isValid \/ Lbl_13 \/ Lbl_14 \/ Lbl_15 \/ Lbl_16
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

INV0_1 == (\A r, c \in 1..N:
  board[r][c] # 0 =>
  (\E k, l \in 1..N:
    (\A m, n \in 1..N: m # n => board[r][m] # board[r][n]) /\ (\A m, n \in 1..N: m # n => board[m][c] # board[n][c]) /\
    ((r = k) \/ (c = l) \/ ((r-1) % SQRT_N = (k-1) % SQRT_N /\ (c-1) % SQRT_N = (l-1) % SQRT_N)) /\
    board[k][l] = board[r][c]))



=============================================================================
\* There does not exist a number I can put in every board[row][col] that will make my solution valid

\* There exists no valid configuration

\* For all configurations that fill out my board, they arent valid

\* 

\*  

\* Modification History
\* Last modified Tue Apr 11 00:05:42 EDT 2023 by chiddy00
\* Created Mon Apr 10 22:19:41 EDT 2023 by chiddy00
