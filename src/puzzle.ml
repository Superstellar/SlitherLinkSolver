let z3ctx = Constraint.z3ctx

let solver = Constraint.solver


let r_box0 =
  let open Constraint in
  make_rule [ varx; vary; varz; varw ]
    (Z3.Boolean.mk_implies z3ctx
      (Z3.FuncDecl.apply box0 [ varx; vary; varz; varw ])
      (num_among_edge_is_colored 0 [ varx; vary; varz; varw ]))

let r_box1 =
  let open Constraint in
  make_rule [ varx; vary; varz; varw ]
    (Z3.Boolean.mk_implies z3ctx
      (Z3.FuncDecl.apply box1 [ varx; vary; varz; varw ])
      (num_among_edge_is_colored 1 [ varx; vary; varz; varw ]))

let r_box2 =
  let open Constraint in
  make_rule [ varx; vary; varz; varw ]
    (Z3.Boolean.mk_implies z3ctx
      (Z3.FuncDecl.apply box2 [ varx; vary; varz; varw ])
      (num_among_edge_is_colored 2 [ varx; vary; varz; varw ]))

let r_box3 =
  let open Constraint in
  make_rule [ varx; vary; varz; varw ]
    (Z3.Boolean.mk_implies z3ctx
      (Z3.FuncDecl.apply box3 [ varx; vary; varz; varw ])
      (num_among_edge_is_colored 3 [ varx; vary; varz; varw ]))

let r_corner0 = 
  let open Constraint in
  make_rule [ varx; vary; varz; varw ]
    (Z3.Boolean.mk_implies z3ctx
      (Z3.FuncDecl.apply corner [ varx; vary; varz; varw ])
      (Z3.Boolean.mk_or z3ctx 
        [
          (num_among_edge_is_colored 2 [ varx; vary; varz; varw ]);
          (num_among_edge_is_colored 0 [ varx; vary; varz; varw ]);
        ]))

let r_path0 = 
  let open Constraint in
  make_rule [ varx; vary ]
    (Z3.Boolean.mk_implies z3ctx
      (Z3.Boolean.mk_and z3ctx
        [
          Z3.FuncDecl.apply colored [ varx ];
          Z3.FuncDecl.apply colored [ vary ];
          Z3.FuncDecl.apply adjacent [ varx; vary ];
        ])
      (Z3.FuncDecl.apply path [ varx; vary ]))

let r_path1 = 
  let open Constraint in
  make_rule [ varx; vary; varz ]
    (Z3.Boolean.mk_implies z3ctx
      (Z3.Boolean.mk_and z3ctx
        [
          Z3.FuncDecl.apply path [ varx; vary ];
          Z3.FuncDecl.apply path [ vary; varz ];
        ])
    (Z3.FuncDecl.apply path [ varx; varz ]))

let _ =
  Z3.Symbol.mk_string z3ctx "r_box0"
  |> Option.some
  |> Z3.Fixedpoint.add_rule solver r_box0;
  Z3.Symbol.mk_string z3ctx "r_box1"
  |> Option.some
  |> Z3.Fixedpoint.add_rule solver r_box1;
  Z3.Symbol.mk_string z3ctx "r_box2"
  |> Option.some
  |> Z3.Fixedpoint.add_rule solver r_box2;
  Z3.Symbol.mk_string z3ctx "r_box3"
  |> Option.some
  |> Z3.Fixedpoint.add_rule solver r_box3;
  Z3.Symbol.mk_string z3ctx "r_corner0"
  |> Option.some
  |> Z3.Fixedpoint.add_rule solver r_corner0;
  Z3.Symbol.mk_string z3ctx "r_path0"
  |> Option.some
  |> Z3.Fixedpoint.add_rule solver r_path0;
  Z3.Symbol.mk_string z3ctx "r_path1"
  |> Option.some
  |> Z3.Fixedpoint.add_rule solver r_path1

let edge_to_index height width is_hor row_num col_num =
  if is_hor
    then (row_num + 1) * (width + 2) + (col_num + 1)
    else (width + 2) * (height + 1) + (row_num + 1) * (width + 1) + (col_num + 1)
let index_to_edge height width index = 
  if index < (width + 2) * (height + 1) then
    (true, index / (width + 2) - 1, index mod (width + 2) - 1)
  else 
    let index = index - (width + 2) * (height + 1) in
    (false, index / (width + 1) - 1, index mod (width + 1) - 1)

let setup_grid solver height width box_num_list = 
  let add_fact = Z3.Fixedpoint.add_fact solver in
  let hor_index = edge_to_index height width true in
  let ver_index = edge_to_index height width false in
  let _ = List.init (height + 1) (fun row_num -> List.init (width + 1) (fun col_num -> 
    let e1 = hor_index row_num col_num in
    let e2 = ver_index row_num col_num in
    let e3 = hor_index row_num (col_num-1) in
    let e4 = ver_index (row_num-1) col_num in
    add_fact Constraint.corner [ e1; e2; e3; e4 ];
    add_fact Constraint.adjacent [ e1; e2 ];
    add_fact Constraint.adjacent [ e1; e3 ];
    add_fact Constraint.adjacent [ e1; e4 ];
    add_fact Constraint.adjacent [ e2; e3 ];
    add_fact Constraint.adjacent [ e2; e4 ];
    add_fact Constraint.adjacent [ e3; e4 ];
    add_fact Constraint.adjacent [ e4; e3 ];
    add_fact Constraint.adjacent [ e4; e2 ];
    add_fact Constraint.adjacent [ e3; e2 ];
    add_fact Constraint.adjacent [ e4; e1 ];
    add_fact Constraint.adjacent [ e3; e1 ];
    add_fact Constraint.adjacent [ e2; e1 ])) in
  List.iter (fun (row_num, col_num, box_num) ->
    assert ((box_num >= 0) && (box_num < 4));
    let box_funcdecl_list = [| Constraint.box0; Constraint.box1; Constraint.box2; Constraint.box3 |] in
    add_fact box_funcdecl_list.(box_num) [
      hor_index row_num col_num; 
      ver_index row_num col_num;
      hor_index (row_num+1) col_num;
      ver_index row_num (col_num+1);] ) box_num_list

let question = 
  let open Constraint in
  make_rule [ varx; vary ]
    (Z3.Boolean.mk_implies z3ctx
      (Z3.Boolean.mk_and z3ctx
        [ Z3.FuncDecl.apply colored [ varx ]; Z3.FuncDecl.apply colored [ vary ] ])
      (Z3.FuncDecl.apply path [ varx; vary ]))