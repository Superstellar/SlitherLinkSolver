let z3ctx = Z3.mk_context [ ("model", "true"); ("unsat_core", "true") ]

let solver = Z3.Solver.mk_solver z3ctx None

let height = 7
let width = 7
let box_bits = 6

let puzzle_box = Z3.BitVector.mk_sort z3ctx box_bits

let box_set = Z3.Set.mk_sort z3ctx puzzle_box

let boolean_sort = Z3.Boolean.mk_sort z3ctx

let i3_sort = Z3.BitVector.mk_sort z3ctx 3

(* relation *)

let colored =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Colored" [ puzzle_box ] boolean_sort

let box_fun_up = 
  Z3.FuncDecl.mk_func_decl_s z3ctx "BoxUp" [ puzzle_box ] puzzle_box
let box_fun_left = 
  Z3.FuncDecl.mk_func_decl_s z3ctx "BoxLeft" [ puzzle_box ] puzzle_box

let connected =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Connected" [ puzzle_box ] puzzle_box

(* for making rules *)
let varx = Z3.Expr.mk_const_s z3ctx "X" puzzle_box
let vary = Z3.Expr.mk_const_s z3ctx "Y" puzzle_box
let varz = Z3.Expr.mk_const_s z3ctx "Z" puzzle_box
let varup = Z3.Expr.mk_const_s z3ctx "X_UP" puzzle_box
let vardown = Z3.Expr.mk_const_s z3ctx "X_DOWN" puzzle_box
let varleft = Z3.Expr.mk_const_s z3ctx "X_LEFT" puzzle_box 
let varright = Z3.Expr.mk_const_s z3ctx "X_RIGHT" puzzle_box
let varset = Z3.Expr.mk_const_s z3ctx "S" box_set

let mk_forall vars cons = 
  Z3.Quantifier.mk_forall_const z3ctx vars cons None [] [] None None
  |> Z3.Quantifier.expr_of_quantifier

(* utility functions dealing box, position, and color *)

let box_expr (row, col) = Z3.BitVector.mk_numeral z3ctx (string_of_int ((row * width) + col)) box_bits

let pos_up (row, col): int * int = ((if row - 1 < 0 then row - 1 + height else row - 1), col)
let pos_down (row, col): int * int = ((if row + 1 >= height then row + 1 - height else row + 1), col)
let pos_left (row, col): int * int = (row, (if col - 1 < 0 then col - 1 + width else col - 1))
let pos_right (row, col): int * int = (row, (if col + 1 >= width then col + 1 - width else col + 1))

let color_of e = Z3.FuncDecl.apply colored [ e ]
let box_up_of e = Z3.FuncDecl.apply box_fun_up [ e ]
let box_left_of e = Z3.FuncDecl.apply box_fun_left [ e ]
let boxes_adjacent e1 e2 =
  let mk_eq = Z3.Boolean.mk_eq z3ctx in
  Z3.Boolean.mk_or z3ctx 
    [ mk_eq (box_up_of e1) (e2);
      mk_eq (box_up_of e2) (e1);
      mk_eq (box_left_of e1) (e2);
      mk_eq (box_left_of e2) (e1); ]
let conn_of e = Z3.FuncDecl.apply connected [ e ]

let diff_colored e1 e2 = Z3.Boolean.mk_xor z3ctx (color_of e1) (color_of e2)

let i3 = Array.init 4 (fun i -> Z3.BitVector.mk_numeral z3ctx (string_of_int i) 3)

let color_of_pos pos = pos |> box_expr |> color_of

(* let combinations l r = 
  assert ((r >= 0) && (List.length l >= r));
  let rec comb l n r cur c =
    (match l with
    | [] -> [c]
    | expr :: l_tail -> if cur >= r then
        comb l_tail (n-1) r cur (mk_not expr :: c)
      else if cur <= r - n then
        comb l_tail (n-1) r (cur+1) (expr :: c)
      else List.append
      (comb l_tail (n-1) r cur (mk_not expr :: c))
      (comb l_tail (n-1) r (cur+1) (expr :: c))) in
  comb l (List.length l) r 0 [] *)
