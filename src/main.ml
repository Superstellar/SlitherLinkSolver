module F = Format

type context = Constraint.context

let read_box_num row s = 
  let s = s |> String.to_seqi |> List.of_seq in
  let f = fun (col, ch) -> (match ch with
    | '0' -> Some (row, col, 0)
    | '1' -> Some (row, col, 1)
    | '2' -> Some (row, col, 2)
    | '3' -> Some (row, col, 3)
    | _ -> None) in
  List.filter_map f s
let read_input = function 
  | height :: width :: box_list -> (
    int_of_string height,
    int_of_string width,
    List.concat (List.mapi read_box_num box_list))
  | _ -> failwith "Input file is too short"
let rec read_chan chan lines = 
  try read_chan chan (input_line chan :: lines)
  with End_of_file -> close_in chan; List.rev lines

let print_model (ctx:context) model = 
  let _ = List.init ctx.height (fun row ->
    let _ = List.init ctx.width (fun col ->
      let pos = Constraint.pos_from_rc ctx row col in
      let color = Z3.Model.eval model ctx.color_of.(pos) false |> Option.get |> Z3.Expr.to_string |> bool_of_string in
      if color then F.printf "O" else F.printf "-"
    ) in F.printf "\n";
  ) in ()
let check (ctx:context) = 
  let status = Z3.Solver.check ctx.solver [] in
  match status with
  | Z3.Solver.SATISFIABLE ->
    let model = ctx.solver |> Z3.Solver.get_model |> Option.get in
    F.printf "Can solve\n";
    print_model ctx model;
    Puzzle.remove_model ctx model;
    (match Z3.Solver.check ctx.solver [] with
      | Z3.Solver.SATISFIABLE ->
        let model = ctx.solver |> Z3.Solver.get_model |> Option.get in
        F.printf "Duplicate answer\n";
        print_model ctx model
      | Z3.Solver.UNKNOWN ->
        F.printf "Unknown\n"
      | Z3.Solver.UNSATISFIABLE ->
        F.printf "Unique answer\n";);
    true
  | Z3.Solver.UNKNOWN ->
    F.printf "Unknown\n";
    false
  | Z3.Solver.UNSATISFIABLE ->
    F.printf "Cannot solve\n";
    let unsat_core = Z3.Solver.get_unsat_core ctx.solver in
    List.iteri (fun i e -> F.printf "Assertion %3d:\n%s\n" i (e |> Z3.Expr.ast_of_expr |> Z3.AST.to_string)) unsat_core;
    false

let main argv = 
  if Array.length argv <> 2 then (
    prerr_endline "solver: You must specify one input file";
    prerr_endline "Usage: solver [ filename of input ]";
    exit 1);
  let (height, width, box_num_list) = read_chan (open_in argv.(1)) [] |> read_input in
  let ctx = Constraint.mk_context height width in
  Puzzle.add_rules ctx box_num_list;
  let _ = check ctx in
  ()

  
let _ = main Sys.argv