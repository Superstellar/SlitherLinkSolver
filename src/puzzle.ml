let z3ctx = Constraint.z3ctx

let solver = Constraint.solver


let r_box_pos = 
  let open Constraint in
  List.init height (fun row ->
    List.init width (fun col ->
      let pos = (row, col) in
      let box = pos |> box_expr in
      [
        (Z3.Boolean.mk_eq z3ctx 
          (Z3.FuncDecl.apply box_fun_up [ box ])
          (pos |> pos_up |> box_expr));
        (Z3.Boolean.mk_eq z3ctx 
          (Z3.FuncDecl.apply box_fun_left [ box ])
          (pos |> pos_left |> box_expr));
      ]
      )) 
  |> List.concat |> List.concat

let r_boundaries =
  let open Constraint in
  List.init height (fun row ->
    List.init width (fun col ->
      if (row = 0) || (row = height - 1) || (col = 0) || (col = width - 1)
        then Some ((row, col) |> box_expr |> color_of |> Z3.Boolean.mk_not z3ctx)
        else None)) 
  |> List.concat
  |> List.filter_map (fun e -> e)

let r_box box_num_list =
  let open Constraint in
  let box_expr_to_i3 e1 e2 = 
    Z3.Boolean.mk_ite z3ctx (diff_colored e1 e2) i3.(1) i3.(0) in
  let i3_sum_of_four e1 e2 e3 e4 =
    (let mk_add = Z3.BitVector.mk_add z3ctx in
    mk_add (mk_add (mk_add e1 e2) e3) e4) in
  List.map (fun (row, col, box_num) ->
    let pos = (row+1, col+1) in
    let box = pos |> box_expr in
    let actual_number = i3_sum_of_four 
      (box_expr_to_i3 box (pos |> pos_up |> box_expr))
      (box_expr_to_i3 box (pos |> pos_down |> box_expr))
      (box_expr_to_i3 box (pos |> pos_left |> box_expr))
      (box_expr_to_i3 box (pos |> pos_right |> box_expr)) in
    let expected_number = i3.(box_num) in
    Z3.Boolean.mk_eq z3ctx actual_number expected_number
  ) box_num_list

let r_connect0 =
  let open Constraint in
  mk_forall [ varset; varx; vary; varz ]
  (Z3.Boolean.mk_implies z3ctx 
    (Z3.Boolean.mk_and z3ctx
      [ (Z3.Boolean.mk_eq z3ctx varset (Z3.Set.mk_empty z3ctx puzzle_box));
        (Z3.Boolean.mk_implies z3ctx
          (Z3.Boolean.mk_and z3ctx [
            Z3.Set.mk_membership z3ctx varx varset;
            Z3.Boolean.mk_not z3ctx (color_of varx);
            Z3.Boolean.mk_not z3ctx (color_of vary);
            boxes_adjacent varx vary; ])
          (Z3.Set.mk_membership z3ctx vary varset));
      ])
    (Z3.Boolean.mk_iff z3ctx
      (Z3.Set.mk_membership z3ctx varz varset)
      (Z3.Boolean.mk_not z3ctx (color_of varz)))
  )

let r_connect1 =
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
  )

let add_rules box_num_list = 
  (* let mk_boolean = Z3.Boolean.mk_const_s z3ctx in *)
  (* let mk_boolean_list s len = List.init len (fun i -> mk_boolean (Format.sprintf "%s_%d" s i)) in *)
  (* Z3.Solver.assert_and_track_l solver r_box_pos (mk_boolean_list "R_pos" (List.length r_box_pos)); *)
  (* Z3.Solver.assert_and_track_l solver r_boundaries (mk_boolean_list "R_bd" (List.length r_boundaries)); *)
  (* Z3.Solver.assert_and_track_l solver (r_box box_num_list) (mk_boolean_list "R_box" (List.length box_num_list)); *)
  (* Z3.Solver.assert_and_track_l solver [ r_connect0; r_connect1 ] (mk_boolean_list "R_con" 2); *)
  Z3.Solver.add solver r_box_pos;
  Z3.Solver.add solver r_boundaries;
  Z3.Solver.add solver (r_box box_num_list);
  Format.printf "r_connect0:\n%s\nr_connect1:\n%s\n" (Z3.Expr.to_string r_connect0) (Z3.Expr.to_string r_connect1);
  Z3.Solver.add solver [ r_connect0; r_connect0 ];