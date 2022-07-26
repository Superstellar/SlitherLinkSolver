let z3ctx = Z3.mk_context [ ("model", "true"); ("unsat_core", "true") ]

let solver = Z3.Solver.mk_solver z3ctx None

let height = 9
let width = 9

let box_total = width * height
let pos_row pos = pos / width
let pos_col pos = pos mod width
let pos_from_rc row col = (row * width) + col
let pos_up pos = let pos = pos - width in if pos < 0 then pos + box_total else pos
let pos_down pos = let pos = pos + width in if pos >= box_total then pos - box_total else pos
let pos_left pos = if pos_col pos = 0 then pos + width - 1 else pos - 1
let pos_right pos = if pos_col pos = width - 1 then pos + 1 - width else pos + 1

let puzzle_box_str = 
  List.init height (fun row ->
    List.init width (fun col -> 
      Format.sprintf "box_%d_%d" row col))
  |> List.concat

let puzzle_box = Z3.Enumeration.mk_sort_s z3ctx "BOX" puzzle_box_str

let box_set = Z3.Set.mk_sort z3ctx puzzle_box

let boolean_sort = Z3.Boolean.mk_sort z3ctx

(* relation *)

let box_fun_up = 
  Z3.FuncDecl.mk_func_decl_s z3ctx "BoxUp" [ puzzle_box ] puzzle_box
let box_fun_left = 
  Z3.FuncDecl.mk_func_decl_s z3ctx "BoxLeft" [ puzzle_box ] puzzle_box

(* for making rules *)
let varx = Z3.Expr.mk_const_s z3ctx "X" puzzle_box
let vary = Z3.Expr.mk_const_s z3ctx "Y" puzzle_box
let colored = Z3.Expr.mk_const_s z3ctx "Color" box_set
let varset = Z3.Expr.mk_const_s z3ctx "S" box_set

let mk_forall vars cons = 
  Z3.Quantifier.mk_forall_const z3ctx vars cons None [] [] None None
  |> Z3.Quantifier.expr_of_quantifier

(* utility functions dealing box, position, and color *)

let box_expr pos = Z3.Enumeration.get_const puzzle_box pos


let color_of b = Z3.Set.mk_membership z3ctx b colored
let box_up_of b = Z3.FuncDecl.apply box_fun_up [ b ]
let box_left_of b = Z3.FuncDecl.apply box_fun_left [ b ]
let boxes_adjacent b1 b2 =
  let mk_eq = Z3.Boolean.mk_eq z3ctx in
  Z3.Boolean.mk_or z3ctx 
    [ mk_eq (box_up_of b1) (b2);
      mk_eq (box_up_of b2) (b1);
      mk_eq (box_left_of b1) (b2);
      mk_eq (box_left_of b2) (b1); ]
let boxes_adjacent5 b b_up b_down b_left b_right = 
  let mk_eq = Z3.Boolean.mk_eq z3ctx in
  Z3.Boolean.mk_and z3ctx
    [ mk_eq (box_up_of b) (b_up);
      mk_eq (box_up_of b_down) (b);
      mk_eq (box_left_of b) (b_left);
      mk_eq (box_left_of b_right) (b); ]

let boxes_diagonal b b_up b_left b_diag =
  let mk_eq = Z3.Boolean.mk_eq z3ctx in
  Z3.Boolean.mk_and z3ctx 
    [ mk_eq (box_up_of b) (b_up);
      mk_eq (box_left_of b) (b_left);
      mk_eq (box_left_of b_up) (b_diag); ]

let diff_colored e1 e2 = Z3.Boolean.mk_xor z3ctx (color_of e1) (color_of e2)

let color_of_pos pos = pos |> box_expr |> color_of

let four_box_of i b b0 b1 b2 b3 = 
  let e0 = diff_colored b b0 in
  let e1 = diff_colored b b1 in
  let e2 = diff_colored b b2 in
  let e3 = diff_colored b b3 in
  let n = Z3.Boolean.mk_not z3ctx in
  let y = (fun x: Z3.Expr.expr -> x) in
  let a = Z3.Boolean.mk_and z3ctx in
  let o = Z3.Boolean.mk_or z3ctx in
  match i with
  | 0 -> a [n e0; n e1; n e2; n e3]
  | 1 -> o [a [y e0; n e1; n e2; n e3]; a [n e0; y e1; n e2; n e3]; a [n e0; n e1; y e2; n e3]; a [n e0; n e1; n e2; y e3];]
  | 2 -> o [a [y e0; y e1; n e2; n e3]; a [y e0; n e1; y e2; n e3]; a [y e0; n e1; n e2; y e3]; a [n e0; y e1; y e2; n e3]; a [n e0; y e1; n e2; y e3]; a [n e0; n e1; y e2; y e3];]
  | 3 -> o [a [y e0; y e1; y e2; n e3]; a [y e0; y e1; n e2; y e3]; a [y e0; n e1; y e2; y e3]; a [n e0; y e1; y e2; y e3];]
  | _ -> failwith "Inappropriate in-box number"

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
