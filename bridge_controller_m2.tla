------------------------ MODULE bridge_controller_m2 ------------------------
EXTENDS Integers, Naturals, Sequenes, TLC
CONSTANT d, bound, COLOR
AXIOM /\ d \in Nat
      /\ d > 0
      /\ COLOR = {green, red}
      /\ green /= red

(*
--algorithm bridgeController_m2 {
    variable a = 0, b = 0, c = 0, ml_tl = red, il_tl = red, ml_pass = 1, il_pass = 1;
    
    
    procedure ML_tl_green() {
        ml_tl := green;
        il_tl := red;
        ml_pass := 0;
        return;
    }
    
    procedure IL_tl_green() {
        il_tl := green;
        ml_tl := red;
        il_pass := 0;
        return;
    }
    
    procedure ML_out_1() {
        a := a + 1;
        ml_pass := 1;
        return;
    }
    
    procedure ML_out_2() {
        a := a + 1;
        ml_tl := red;
        ml_pass := 1;
        return;
    }
    
    procedure IL_out_1() {
        b := b - 1;
        c := c + 1;
        il_pass := 1;
        return;
    }
    
    procedure IL_out_2() {
        b := b - 1;
        c := c + 1;
        il_tl := red;
        il_pass := 1;
        return;
    }
    
    procedure ML_in() {
        c := c - 1;
        return;
    }
    
    procedure IL_in() {
        a := a - 1;
        b := b + 1;
        return;
    }
    
    \* main method
    {
        while(i < bound) {
            either {
                if() {
                
                };
            }
            or {
                if() {
                };
            }
            or {
                if() {
                };
            }
            or {
                if() {
                };
            }
            or {
                if() {
                };
            }
            or {
                if() {
                };
            }
            or {
                if() {
                };
            }
            or {
                if() {
                };
            };
            
            i := i + 1;
        }
    }
}
*)

=============================================================================
\* Modification History
\* Last modified Sun Feb 05 18:45:35 EST 2023 by chiddy00
\* Created Sun Feb 05 18:14:56 EST 2023 by chiddy00
