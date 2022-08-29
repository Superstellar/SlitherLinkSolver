type context = Constraint.context

let r_boundaries ctx =
  let open Constraint in
  List.init ctx.box_total (fun pos ->
    let row = pos_row ctx pos in
    let col = pos_col ctx pos in
    if (row = 0) || (row = ctx.height - 1) || (col = 0) || (col = ctx.width - 1)
      then Some (ctx.var.(pos) |> Z3.Boolean.mk_not ctx.z3ctx)
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
    [ mk_implies (mk_and [ctx.var.(b1); ctx.var.(b2)]) (mk_or [ctx.var.(b0); ctx.var.(b3)]);
      mk_implies (mk_and [ctx.var.(b0); ctx.var.(b3)]) (mk_or [ctx.var.(b1); ctx.var.(b2)]); ])
  |> List.concat

let r_invariant ctx = 
  let open Constraint in
  let invar = get_invariant ctx in
  Z3.Boolean.mk_eq ctx.z3ctx invar (Z3.Arithmetic.Integer.mk_numeral_i ctx.z3ctx 1)

let add_rules (ctx:context) box_num_list = 
  let add = Z3.Solver.add ctx.solver in
  add (r_boundaries ctx);
  add (r_box ctx box_num_list);
  add (r_box_diag ctx);
  add [r_invariant ctx]
  (* Format.printf "r_connect0:\n%s\nr_connect1:\n%s\n" (Z3.Expr.to_string r_connect0) (Z3.Expr.to_string r_connect1); *)
  (* Z3.Solver.add solver [ r_connect0; r_connect0 ]; *)
  (* List.iter (fun e -> Format.printf "%s\n" (Z3.Expr.to_string e)) (Z3.Solver.get_assertions solver) *)

let remove_model (ctx:context) model = 
  let eval pos = Z3.Model.eval model ctx.var.(pos) false |> Option.get in
  [ List.init ctx.box_total (fun b -> Z3.Boolean.mk_eq ctx.z3ctx ctx.var.(b) (eval b))
    |> Z3.Boolean.mk_and ctx.z3ctx 
    |> Z3.Boolean.mk_not ctx.z3ctx ]
  |> Z3.Solver.add ctx.solver