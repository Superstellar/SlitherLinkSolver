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
  let box_numeral_max = 
    Z3.BitVector.mk_numeral z3ctx (("0b" ^ (String.make box_bits '1')) |> int_of_string |> string_of_int) box_bits in
  let box_num_on_color e1 e2 = 
    Z3.Boolean.mk_ite z3ctx (diff_colored e1 e2) box_numeral_max (conn_of e2) in
  let min_box e1 e2 = 
    Z3.Boolean.mk_ite z3ctx (Z3.BitVector.mk_ult z3ctx e1 e2) e1 e2 in
  let min_of_five e1 e2 e3 e4 e5 =
    min_box (min_box (min_box (min_box e1 e2) e3) e4) e5 in
  make_rule [ varx; varup; vardown; varleft; varright ]
  (Z3.Boolean.mk_implies z3ctx
    (Z3.Boolean.mk_and z3ctx 
      [
        Z3.Boolean.mk_eq z3ctx (box_up_of varx) varup;
        Z3.Boolean.mk_eq z3ctx (box_up_of vardown) varx;
        Z3.Boolean.mk_eq z3ctx (box_left_of varx) varleft;
        Z3.Boolean.mk_eq z3ctx (box_left_of varright) varx;
      ])
    (Z3.Boolean.mk_eq z3ctx
      (conn_of varx)
      (min_of_five
        varx
        (box_num_on_color varx varup)
        (box_num_on_color varx vardown)
        (box_num_on_color varx varleft)
        (box_num_on_color varx varright))))

let r_connect1 =
  let open Constraint in
  let max_box_expr = box_expr (height - 1, width - 1) in
  make_rule [ varx; vary ]
  (Z3.Boolean.mk_implies z3ctx
    (Z3.Boolean.mk_and z3ctx [
      Z3.BitVector.mk_ule z3ctx varx max_box_expr;
      Z3.BitVector.mk_ule z3ctx vary max_box_expr; ])
    (Z3.Boolean.mk_iff z3ctx
      (Z3.Boolean.mk_not z3ctx (diff_colored varx vary))
      (Z3.Boolean.mk_eq z3ctx (conn_of varx) (conn_of vary)))
  )

let add_rules box_num_list = 
  let mk_boolean = Z3.Boolean.mk_const_s z3ctx in
  let mk_boolean_list s len = List.init len (fun i -> mk_boolean (Format.sprintf "%s_%d" s i)) in
  (* Z3.Solver.assert_and_track_l solver r_box_pos (mk_boolean_list "R_pos" (List.length r_box_pos)); *)
  (* Z3.Solver.assert_and_track_l solver r_boundaries (mk_boolean_list "R_bd" (List.length r_boundaries)); *)
  (* Z3.Solver.assert_and_track_l solver (r_box box_num_list) (mk_boolean_list "R_box" (List.length box_num_list)); *)
  (* Z3.Solver.assert_and_track_l solver [ r_connect0; r_connect1 ] (mk_boolean_list "R_con" 2); *)
  Z3.Solver.add solver r_box_pos;
  Z3.Solver.add solver r_boundaries;
  Z3.Solver.add solver (r_box box_num_list);
  (* Format.printf "r_connect0:\n%s\nr_connect1:\n%s\n" (Z3.Expr.to_string r_connect0) (Z3.Expr.to_string r_connect1); *)
  Z3.Solver.add solver [ r_connect0; r_connect1 ];
  (* Z3.Solver.add solver [ r_connect0; r_connect1 ]; *)