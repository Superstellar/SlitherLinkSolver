let z3ctx = Z3.mk_context [ ("model", "true"); ("unsat_core", "true") ]

let solver = 
  let mk_string_symbol s = Z3.Symbol.mk_string z3ctx s in
  let s = Z3.Fixedpoint.mk_fixedpoint z3ctx in
  let param = Z3.Params.mk_params z3ctx in
  Z3.Params.add_symbol param
    (mk_string_symbol "engine")
    (mk_string_symbol "datalog");
  Z3.Fixedpoint.set_parameters s param;
  s

let puzzle_edge = Z3.FiniteDomain.mk_sort_s z3ctx "puzzle_edge" 65536

let boolean_sort = Z3.Boolean.mk_sort z3ctx

let integer_sort = Z3.Arithmetic.Integer.mk_sort z3ctx

(* relation *)

let colored =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Colored" [ puzzle_edge ] boolean_sort

let adjacent =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Adjacent" [ puzzle_edge; puzzle_edge ] boolean_sort

let path =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Path" [ puzzle_edge; puzzle_edge ] boolean_sort

let corner =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Corner" [ puzzle_edge; puzzle_edge; puzzle_edge; puzzle_edge ] boolean_sort

let box0 =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Box0" [ puzzle_edge; puzzle_edge; puzzle_edge; puzzle_edge ] boolean_sort

let box1 =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Box1" [ puzzle_edge; puzzle_edge; puzzle_edge; puzzle_edge ] boolean_sort

let box2 =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Box2" [ puzzle_edge; puzzle_edge; puzzle_edge; puzzle_edge ] boolean_sort

let box3 =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Box3" [ puzzle_edge; puzzle_edge; puzzle_edge; puzzle_edge ] boolean_sort
      

(* for making rules *)
let varx = Z3.Expr.mk_const_s z3ctx "X" puzzle_edge
let vary = Z3.Expr.mk_const_s z3ctx "Y" puzzle_edge
let varz = Z3.Expr.mk_const_s z3ctx "Z" puzzle_edge
let varw = Z3.Expr.mk_const_s z3ctx "W" puzzle_edge

let make_rule vars cons = 
  Z3.Quantifier.mk_forall_const z3ctx vars cons None [] [] None None
  |> Z3.Quantifier.expr_of_quantifier

let _ = 
  Z3.Fixedpoint.register_relation solver colored;
  Z3.Fixedpoint.register_relation solver adjacent;
  Z3.Fixedpoint.register_relation solver path

(* utility functions dealing with box/corner *)

let mk_eq = Z3.Boolean.mk_eq z3ctx

let plus_int expr i = 
  Z3.Arithmetic.mk_add z3ctx [ expr;  Z3.Arithmetic.Integer.mk_numeral_i z3ctx i ]

(* from e1 to e4, E -> S -> W -> N *)
(* let has_same_corner e1 e2 e3 e4 = 
  let row_num = row_of e1 in
  let col_num = col_of e1 in
  let row_num_1 = plus_int row_num (-1) in
  let col_num_1 = plus_int col_num (-1) in
  Z3.Boolean.mk_and z3ctx
  [
    Z3.FuncDecl.apply horizontal [ e1 ];
    Z3.FuncDecl.apply vertical [ e2 ];
    Z3.FuncDecl.apply horizontal [ e3 ];
    Z3.FuncDecl.apply vertical [ e4 ];
    mk_eq row_num (row_of e2); 
    mk_eq col_num (col_of e2);
    mk_eq row_num (row_of e3); 
    mk_eq col_num_1 (col_of e3);
    mk_eq row_num_1 (row_of e4); 
    mk_eq col_num (col_of e4);
  ] *)

(* from e1 to e4, top -> right -> bottom -> left *)
(* let has_box_of e1 e2 e3 e4 box_row box_col =
  let box_row_1 = Z3.Arithmetic.Integer.mk_numeral_i (box_row + i) in
  let box_col_1 = Z3.Arithmetic.Integer.mk_numeral_i (box_col + i) in
  let box_row = Z3.Arithmetic.Integer.mk_numeral_i box_row in
  let box_col = Z3.Arithmetic.Integer.mk_numeral_i box_col in
  Z3.Boolean.mk_and z3ctx
  [
    Z3.FuncDecl.apply horizontal [ e1 ];
    Z3.FuncDecl.apply vertical [ e2 ];
    Z3.FuncDecl.apply horizontal [ e3 ];
    Z3.FuncDecl.apply vertical [ e4 ];
    mk_eq box_row (row_of e1); 
    mk_eq box_col (col_of e1);
    mk_eq box_row (row_of e2); 
    mk_eq box_col_1 (col_of e2);
    mk_eq box_row_1 (row_of e3); 
    mk_eq box_col (col_of e3);
    mk_eq box_row (row_of e4); 
    mk_eq box_col (col_of e4);
  ] *)

(* utility functions dealing with boolean expressions *)

let true_term = Z3.Boolean.mk_true z3ctx

let false_term = Z3.Boolean.mk_false z3ctx

let mk_not = Z3.Boolean.mk_not z3ctx

let combinations l r = 
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
  comb l (List.length l) r 0 []

let or_and_expr = function
  | [and_list] -> 
    Z3.Boolean.mk_and z3ctx and_list
  | or_and_list ->
    Z3.Boolean.mk_or z3ctx
    (List.map 
      (fun and_list -> Z3.Boolean.mk_and z3ctx and_list) 
      or_and_list)

let num_among_edge_is_colored num edge_list = 
  assert (List.length edge_list = 4);
  assert ((num >= 0) && (num <= 4));
  let expr_list = List.map (fun edge -> Z3.FuncDecl.apply colored [ edge ]) edge_list in
  let comb = combinations expr_list num in
  or_and_expr comb