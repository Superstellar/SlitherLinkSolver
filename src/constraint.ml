type context = {
  z3ctx: Z3.context; 
  solver: Z3.Solver.solver; 
  height: int; 
  width: int; 
  box_total: int;
  box_sort: Z3.Sort.sort;
  boolean_sort: Z3.Sort.sort;
  color_of: Z3.Expr.expr array;
  dist_of: Z3.Expr.expr array;
}

let mk_context height width = 
  let z3ctx = Z3.mk_context [ ("model", "true"); ("unsat_core", "true") ] in
  let solver = Z3.Solver.mk_solver z3ctx None in
  let params = Z3.Params.mk_params z3ctx in
  let mk_symbols = Z3.Symbol.mk_strings z3ctx in
  List.iter2 (Z3.Params.add_bool params)
    (mk_symbols ["arith.nl"; "ite_extra_rules"; "randomize" ])
    [false; true; false; ];
  List.iter2 (Z3.Params.add_int params)
    (mk_symbols ["arith.solver"; "restart_strategy"; ])
    [5; 4; ];
  Z3.Solver.set_parameters solver params;
  let height = height + 2 in
  let width = width + 2 in
  let box_total = width * height in
  let puzzle_box_str = 
    List.init height (fun row ->
      List.init width (fun col -> 
        Format.sprintf "box_%d_%d" row col))
    |> List.concat in
  let box_sort = Z3.Enumeration.mk_sort_s z3ctx "Box" puzzle_box_str in
  let boolean_sort = Z3.Boolean.mk_sort z3ctx in
  let color = Z3.FuncDecl.mk_func_decl_s z3ctx "Color" [box_sort] boolean_sort in
  let color_of = Array.init box_total (fun i -> Z3.FuncDecl.apply color [Z3.Enumeration.get_const box_sort i]) in
  let dist = Z3.FuncDecl.mk_func_decl_s z3ctx "Dist" [box_sort] (Z3.Arithmetic.Integer.mk_sort z3ctx) in
  let dist_of = Array.init box_total (fun i -> Z3.FuncDecl.apply dist [Z3.Enumeration.get_const box_sort i]) in
  {
    z3ctx = z3ctx;
    solver = solver;
    height = height;
    width = width;
    box_total = box_total;
    box_sort = box_sort;
    boolean_sort = boolean_sort;
    color_of = color_of;
    dist_of = dist_of;
  }

(* utility functions dealing with positions *)
let pos_row ctx pos = pos / ctx.width
let pos_col ctx pos = pos mod ctx.width
let pos_from_rc ctx row col = (row * ctx.width) + col
let pos_up ctx pos = let pos = pos - ctx.width in if pos < 0 then pos + ctx.box_total else pos
let pos_down ctx pos = let pos = pos + ctx.width in if pos >= ctx.box_total then pos - ctx.box_total else pos
let pos_left ctx pos = if pos_col ctx pos = 0 then pos + ctx.width - 1 else pos - 1
let pos_right ctx pos = if pos_col ctx pos = ctx.width - 1 then pos + 1 - ctx.width else pos + 1

let pos_adj ctx pos = ( pos_up ctx pos, pos_down ctx pos, pos_left ctx pos, pos_right ctx pos )
let pos_4box ctx pos = ( pos, pos_up ctx pos, pos_left ctx pos, pos_left ctx (pos_up ctx pos) )


(* utility functions dealing with z3 expressions *)

let mk_forall ctx vars cons = 
  Z3.Quantifier.mk_forall_const ctx.z3ctx vars cons None [] [] None None
  |> Z3.Quantifier.expr_of_quantifier


(* utility functions dealing with z3 colors *)
let diff_colored ctx b1 b2 = Z3.Boolean.mk_xor ctx.z3ctx (ctx.color_of.(b1)) (ctx.color_of.(b2))

let four_box_of ctx i b = 
  let b0, b1, b2, b3 = pos_adj ctx b in
  let e0 = diff_colored ctx b b0 in
  let e1 = diff_colored ctx b b1 in
  let e2 = diff_colored ctx b b2 in
  let e3 = diff_colored ctx b b3 in
  let n = Z3.Boolean.mk_not ctx.z3ctx in
  let y = (fun x: Z3.Expr.expr -> x) in
  let a = Z3.Boolean.mk_and ctx.z3ctx in
  let o = Z3.Boolean.mk_or ctx.z3ctx in
  match i with
  | 0 -> a [n e0; n e1; n e2; n e3]
  | 1 -> o [a [y e0; n e1; n e2; n e3]; a [n e0; y e1; n e2; n e3]; a [n e0; n e1; y e2; n e3]; a [n e0; n e1; n e2; y e3];]
  | 2 -> o [a [y e0; y e1; n e2; n e3]; a [y e0; n e1; y e2; n e3]; a [y e0; n e1; n e2; y e3]; a [n e0; y e1; y e2; n e3]; a [n e0; y e1; n e2; y e3]; a [n e0; n e1; y e2; y e3];]
  | 3 -> o [a [y e0; y e1; y e2; n e3]; a [y e0; y e1; n e2; y e3]; a [y e0; n e1; y e2; y e3]; a [n e0; y e1; y e2; y e3];]
  | _ -> failwith "Inappropriate in-box number"

let get_invariant ctx = 
  let mk_num = Z3.Arithmetic.Integer.mk_numeral_i ctx.z3ctx in
  let mk_not = Z3.Boolean.mk_not ctx.z3ctx in
  let mk_and = Z3.Boolean.mk_and ctx.z3ctx in
  let mk_add = Z3.Arithmetic.mk_add ctx.z3ctx in
  let mk_bool_int e i = Z3.Boolean.mk_ite ctx.z3ctx e (mk_num i) (mk_num 0) in
  mk_add (
    List.init ctx.box_total (fun pos -> 
      let b0, b1, b2, b3 = pos_4box ctx pos in
      [ mk_bool_int (mk_and [ ctx.color_of.(b0); mk_not ctx.color_of.(b1); mk_not ctx.color_of.(b2) ]) 1;
        mk_bool_int (mk_and [ ctx.color_of.(b0); ctx.color_of.(b1); ctx.color_of.(b2); mk_not ctx.color_of.(b3) ]) (-1); ]
    ) |> List.concat
  )