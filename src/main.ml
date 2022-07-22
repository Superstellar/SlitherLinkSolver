module F = Format

let solver = Constraint.solver

let read_box_num s = 
  let r = Str.regexp {|[0-9]+|} in
  let s1 = Str.search_forward r s 0 + 1 in
  let row_num = s |> Str.matched_string |> int_of_string in
  let s2 = Str.search_forward r s s1 + 1 in
  let col_num = s |> Str.matched_string |> int_of_string in
  let _ = Str.search_forward r s s2 + 1 in
  let box_num = s |> Str.matched_string |> int_of_string in
  (row_num, col_num, box_num)
let read_input = function 
  | height :: width :: box_list -> (
    int_of_string height,
    int_of_string width,
    List.map read_box_num box_list)
  | _ -> failwith "Input file is too short"
let rec read_chan chan lines = 
  try read_chan chan (input_line chan :: lines)
  with End_of_file -> close_in chan; List.rev lines

let main argv = 
  if Array.length argv <> 2 then (
    prerr_endline "solver: You must specify one input file";
    prerr_endline "Usage: solver [ filename of input ]";
    exit 1);
  F.printf "flag 1\n";
  let (_height, _width, box_num_list) = read_chan (open_in argv.(1)) [] |> read_input in
  F.printf "flag 2\n";
  Puzzle.add_rules box_num_list;
  F.printf "flag 3\n";
  let status = Z3.Solver.check solver [] in
  F.printf "flag 4\n";
  match status with
  | Z3.Solver.SATISFIABLE ->
    let model = solver |> Z3.Solver.get_model |> Option.get in
    F.printf "Can solve\n";
    let _ = List.init (Constraint.height) (fun row ->
      let _ = List.init (Constraint.width) (fun col ->
        if (Z3.Model.eval model (Constraint.color_of_pos (row, col)) false |> Option.get |> Z3.Expr.to_string |> bool_of_string)
          then F.printf "O" else F.printf "-"
      ) in F.printf "\n";
    ) in 
    let _ = List.init (Constraint.height) (fun row ->
      let _ = List.init (Constraint.width) (fun col ->
        let _ = (Z3.Model.eval model ((row, col) |> Constraint.box_expr |> (fun e -> [e]) |> Z3.FuncDecl.apply Constraint.connected) false 
          |> Option.get 
          |> Z3.Expr.to_string 
          |> String.mapi (fun i c -> if i=0 then '0' else c)
          |> int_of_string
          |> (fun ind -> (ind / Constraint.width, ind mod Constraint.width))
          |> (fun (r, c) -> F.printf "(%d,%d) " r c)) in ()
      ) in F.printf "\n";
    ) in ()
  | Z3.Solver.UNKNOWN ->
    F.printf "Unknown\n"
  | Z3.Solver.UNSATISFIABLE ->
    F.printf "Cannot solve\n";
    let unsat_core = Z3.Solver.get_unsat_core Constraint.solver in
    List.iteri (fun i e -> F.printf "Assertion %3d:\n%s\n" i (e |> Z3.Expr.ast_of_expr |> Z3.AST.to_string)) unsat_core

let _ = main Sys.argv
