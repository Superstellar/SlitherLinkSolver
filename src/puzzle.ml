type context = Constraint.context

let r_boundaries ctx =
  let open Constraint in
  List.init ctx.box_total (fun pos ->
    let row = pos_row ctx pos in
    let col = pos_col ctx pos in
    if (row = 0) || (row = ctx.height - 1) || (col = 0) || (col = ctx.width - 1)
      then Some (ctx.color_of.(pos) |> Z3.Boolean.mk_not ctx.z3ctx)
      else None)
  |> List.filter_map (fun e -> e)

let r_box ctx box_num_list =
  let open Constraint in
  List.map (fun (row, col, box_num) ->
    let pos = pos_from_rc ctx (row+1) (col+1) in
    four_box_of ctx box_num pos
  ) box_num_list

let r_box_diag ctx = 
  let open Constraint in 
  let mk_implies = Z3.Boolean.mk_implies ctx.z3ctx in
  let mk_and = Z3.Boolean.mk_and ctx.z3ctx in
  let mk_or = Z3.Boolean.mk_or ctx.z3ctx in
  List.init ctx.box_total (fun pos ->
    let b0, b1, b2, b3 = pos_4box ctx pos in
    [ mk_implies (mk_and [ctx.color_of.(b1); ctx.color_of.(b2)]) (mk_or [ctx.color_of.(b0); ctx.color_of.(b3)]);
      mk_implies (mk_and [ctx.color_of.(b0); ctx.color_of.(b3)]) (mk_or [ctx.color_of.(b1); ctx.color_of.(b2)]); ])
  |> List.concat

let r_no_1hole ctx =
  let open Constraint in
  List.init ctx.box_total (fun pos ->
    let b0, b1, b2, b3 = pos_adj ctx pos in
    Z3.Boolean.mk_not ctx.z3ctx
      (Z3.Boolean.mk_and ctx.z3ctx [ 
        diff_colored ctx pos b0;
        diff_colored ctx pos b1;
        diff_colored ctx pos b2;
        diff_colored ctx pos b3; ]))

let r_distance ctx =
  let open Constraint in
  let mk_num = Z3.Arithmetic.Integer.mk_numeral_i ctx.z3ctx in
  let mk_min e1 e2 = Z3.Boolean.mk_ite ctx.z3ctx (Z3.Arithmetic.mk_le ctx.z3ctx e1 e2) e1 e2 in
  let mk_min4 e1 e2 e3 e4 = (mk_min (mk_min (mk_min e1 e2) e3) e4) in
  let color_ite pos e1 e2 = Z3.Boolean.mk_ite ctx.z3ctx ctx.color_of.(pos) e1 e2 in
  let mk_plus1 e = Z3.Arithmetic.mk_add ctx.z3ctx [e; mk_num 1] in
  let mk_or = Z3.Boolean.mk_or ctx.z3ctx in
  let mk_and = Z3.Boolean.mk_and ctx.z3ctx in
  let mk_eq = Z3.Boolean.mk_eq ctx.z3ctx in
  List.init ctx.box_total (fun pos ->
    let b0, b1, b2, b3 = pos_adj ctx pos in
    color_ite pos
      (mk_and [
        Z3.Arithmetic.mk_lt ctx.z3ctx ctx.dist_of.(pos) (mk_num ctx.box_total);
        mk_or [
          mk_eq ctx.dist_of.(pos) (mk_num 0);
          mk_eq ctx.dist_of.(pos) (mk_min4 ctx.dist_of.(b0) ctx.dist_of.(b1) ctx.dist_of.(b2) ctx.dist_of.(b3) |> mk_plus1);
        ];
      ]) 
      (mk_eq ctx.dist_of.(pos) (mk_num ctx.box_total))
  )
  
let r_connect ctx = 
  let open Constraint in
  let mk_eq = Z3.Boolean.mk_eq ctx.z3ctx in
  let mk_or = Z3.Boolean.mk_or ctx.z3ctx in
  let mk_and = Z3.Boolean.mk_and ctx.z3ctx in
  let mk_num = Z3.Arithmetic.Integer.mk_numeral_i ctx.z3ctx in
  let is_zero pos = mk_eq ctx.dist_of.(pos) (mk_num 0) in
  let is_positive pos = Z3.Arithmetic.mk_gt ctx.z3ctx ctx.dist_of.(pos) (mk_num 0) in
  let all_nonzero_except pos = List.init ctx.box_total (fun b -> if b = pos then is_zero b else is_positive b) |> mk_and in
  [ List.init ctx.box_total all_nonzero_except |> mk_or ]
  
let r_invariant ctx = 
  let open Constraint in
  let invar = get_invariant ctx in
  let mk_eq = Z3.Boolean.mk_eq ctx.z3ctx in
  let mk_num = Z3.Arithmetic.Integer.mk_numeral_i ctx.z3ctx in
  [ mk_eq invar (mk_num 1) ]

let add_rules (ctx:context) box_num_list = 
  let add = Z3.Solver.add ctx.solver in
  add (r_boundaries ctx);
  add (r_box ctx box_num_list);
  add (r_box_diag ctx);
  add (r_no_1hole ctx);
  add (r_invariant ctx);
  add (r_distance ctx);
  add (r_connect ctx);
  ()
  (* Format.printf "r_connect0:\n%s\nr_connect1:\n%s\n" (Z3.Expr.to_string r_connect0) (Z3.Expr.to_string r_connect1); *)
  (* Z3.Solver.add solver [ r_connect0; r_connect0 ]; *)
  (* List.iter (fun e -> Format.printf "%s\n" (Z3.Expr.to_string e)) (Z3.Solver.get_assertions solver) *)

let remove_model (ctx:context) model = 
  let eval pos = Z3.Model.eval model ctx.color_of.(pos) false |> Option.get in
  [ List.init ctx.box_total (fun b -> Z3.Boolean.mk_eq ctx.z3ctx ctx.color_of.(b) (eval b))
    |> Z3.Boolean.mk_and ctx.z3ctx 
    |> Z3.Boolean.mk_not ctx.z3ctx ]
  |> Z3.Solver.add ctx.solver