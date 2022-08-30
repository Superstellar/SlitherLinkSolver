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
  let mk_plus1 e = Z3.Arithmetic.mk_add ctx.z3ctx [e; mk_num 1] in
  let mk_or = Z3.Boolean.mk_or ctx.z3ctx in
  let mk_and = Z3.Boolean.mk_and ctx.z3ctx in
  let mk_eq = Z3.Boolean.mk_eq ctx.z3ctx in
  let if_same pos b = Z3.Boolean.mk_ite ctx.z3ctx (mk_eq ctx.color_of.(pos) ctx.color_of.(b)) (mk_plus1 ctx.dist_of.(b)) (mk_num 100) in
  List.init ctx.box_total (fun pos ->
    let b0, b1, b2, b3 = pos_adj ctx pos in
    mk_or [
      mk_eq ctx.dist_of.(pos) (mk_num 0);
      mk_and [
        Z3.Arithmetic.mk_lt ctx.z3ctx ctx.dist_of.(pos) (mk_num 100);
        mk_eq ctx.dist_of.(pos)
          (mk_min (if_same pos b0)
            (mk_min (if_same pos b1)
              (mk_min (if_same pos b2) 
                (if_same pos b3))));
      ]
    ]
  )
  
let r_connect ctx = 
  let open Constraint in
  let mk_eq = Z3.Boolean.mk_eq ctx.z3ctx in
  let mk_or = Z3.Boolean.mk_or ctx.z3ctx in
  let mk_num = Z3.Arithmetic.Integer.mk_numeral_i ctx.z3ctx in
  let is_nonzero pos = Z3.Boolean.mk_not ctx.z3ctx (mk_eq ctx.dist_of.(pos) (mk_num 0)) in
  let all_nonzero_except pos = List.init ctx.box_total (fun b -> if b = 0 || b = pos then None else Some (is_nonzero b)) |> List.filter_map (fun i -> i) in
  [ 
    mk_eq
      (mk_num 0)
      (ctx.dist_of.(0));
    mk_or
      ( List.init ctx.box_total (fun b1 ->
          (Z3.Boolean.mk_and ctx.z3ctx 
            (
              ctx.color_of.(b1) :: 
              (all_nonzero_except b1)
            )
          )
        )
      );
  ]
  


let add_rules (ctx:context) box_num_list = 
  let add = Z3.Solver.add ctx.solver in
  add (r_boundaries ctx);
  add (r_box ctx box_num_list);
  add (r_box_diag ctx);
  add (r_distance ctx);
  add (r_no_1hole ctx);
  add (r_connect ctx)
  (* Format.printf "r_connect0:\n%s\nr_connect1:\n%s\n" (Z3.Expr.to_string r_connect0) (Z3.Expr.to_string r_connect1); *)
  (* Z3.Solver.add solver [ r_connect0; r_connect0 ]; *)
  (* List.iter (fun e -> Format.printf "%s\n" (Z3.Expr.to_string e)) (Z3.Solver.get_assertions solver) *)

let remove_model (ctx:context) model = 
  let eval pos = Z3.Model.eval model ctx.color_of.(pos) false |> Option.get in
  [ List.init ctx.box_total (fun b -> Z3.Boolean.mk_eq ctx.z3ctx ctx.color_of.(b) (eval b))
    |> Z3.Boolean.mk_and ctx.z3ctx 
    |> Z3.Boolean.mk_not ctx.z3ctx ]
  |> Z3.Solver.add ctx.solver