let z3ctx = Constraint.z3ctx

let solver = Constraint.solver


let r_box_pos = 
  let open Constraint in
  List.init box_total (fun pos ->
    let box = box_expr pos in
    let mk_eq = Z3.Boolean.mk_eq z3ctx in
    [ mk_eq (box_up_of box) (pos |> pos_up |> box_expr);
      mk_eq (box_left_of box) (pos |> pos_left |> box_expr); ])
  |> List.concat

let r_boundaries =
  let open Constraint in
  List.init box_total (fun pos ->
    let row = pos_row pos in
    let col = pos_col pos in
    if (row = 0) || (row = height - 1) || (col = 0) || (col = width - 1)
      then Some (pos |> box_expr |> color_of |> Z3.Boolean.mk_not z3ctx)
      else None)
  |> List.filter_map (fun e -> e)

let r_box box_num_list =
  let open Constraint in
  List.map (fun (row, col, box_num) ->
    let pos = pos_from_rc (row+1) (col+1) in
    let b = box_expr pos in
    let b0 = pos |> pos_up |> box_expr in
    let b1 = pos |> pos_down |> box_expr in
    let b2 = pos |> pos_left |> box_expr in
    let b3 = pos |> pos_right |> box_expr in
    four_box_of box_num b b0 b1 b2 b3
  ) box_num_list

let r_box_diag = 
  let open Constraint in 
  let mk_implies = Z3.Boolean.mk_implies z3ctx in
  let mk_and = Z3.Boolean.mk_and z3ctx in
  let mk_or = Z3.Boolean.mk_or z3ctx in
  List.init box_total (fun pos ->
    let b = pos |> box_expr in
    let b_up = pos |> pos_up |> box_expr in
    let b_left = pos |> pos_left |> box_expr in
    let b_diag = pos |> pos_up |> pos_left |> box_expr in
    [ mk_implies (mk_and [color_of b; color_of b_diag]) (mk_or [color_of b_up; color_of b_left]);
      mk_implies (mk_and [color_of b_up; color_of b_left]) (mk_or [color_of b; color_of b_diag]); ])
  |> List.concat

let r_set_size i = 
  let open Constraint in
  let i1 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 1 in
  let i0 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 0 in
  let i_target = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
  let colored_int pos = Z3.Boolean.mk_ite z3ctx (pos |> box_expr |> color_of) i1 i0 in
  let i_calc = Z3.Arithmetic.mk_add z3ctx (List.init box_total colored_int) in
  Z3.Boolean.mk_eq z3ctx i_target i_calc
(* let r_connect0 =
  let open Constraint in
  let mk_implies = Z3.Boolean.mk_implies z3ctx in
  let mk_and = Z3.Boolean.mk_and z3ctx in
  let mk_not = Z3.Boolean.mk_not z3ctx in
  let in_varset e = Z3.Set.mk_membership z3ctx e varset in
  mk_forall [ varset ]
  (mk_implies
    (mk_and [
      (mk_forall [ varx; vary ]
        (mk_implies 
          (mk_and [
            in_varset varx;
            boxes_adjacent varx vary;
            color_of vary;
          ])
          (in_varset vary)));
      Z3.Set.mk_subset z3ctx colored varset;
      mk_not (Z3.Boolean.mk_eq z3ctx varset (Z3.Set.mk_empty z3ctx puzzle_box))
    ])
    (Z3.Boolean.mk_eq z3ctx varset colored)) *)

(* let r_connect1 =
  let open Constraint in
  mk_forall [ varset ]
  (Z3.Boolean.mk_implies z3ctx 
    (Z3.Boolean.mk_and z3ctx
      [ (Z3.Boolean.mk_eq z3ctx varset (Z3.Set.mk_empty z3ctx puzzle_box));
        (mk_forall [ varx; vary ]
          (Z3.Boolean.mk_implies z3ctx
            (Z3.Boolean.mk_and z3ctx [
              Z3.Set.mk_membership z3ctx varx varset;
              color_of varx;
              color_of vary;
              boxes_adjacent varx vary;
            ])
            (Z3.Set.mk_membership z3ctx vary varset)));
      ])
    (mk_forall [ varz ]
      (Z3.Boolean.mk_iff z3ctx
        (Z3.Set.mk_membership z3ctx varz varset)
        (color_of varz)))
  ) *)

let add_rules box_num_list = 
  Z3.Solver.add solver r_box_pos;
  Z3.Solver.add solver r_boundaries;
  Z3.Solver.add solver r_box_diag;
  Z3.Solver.add solver (r_box box_num_list);
  Z3.Solver.push solver;
  Z3.Solver.add solver [r_set_size Constraint.box_total]
  (* Format.printf "r_connect0:\n%s\nr_connect1:\n%s\n" (Z3.Expr.to_string r_connect0) (Z3.Expr.to_string r_connect1); *)
  (* Z3.Solver.add solver [ r_connect0; r_connect0 ]; *)
  (* List.iter (fun e -> Format.printf "%s\n" (Z3.Expr.to_string e)) (Z3.Solver.get_assertions solver) *)

let modify_rule i =
  Z3.Solver.pop solver 1;
  Z3.Solver.push solver;
  Z3.Solver.add solver [r_set_size i]