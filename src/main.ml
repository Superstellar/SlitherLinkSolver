module F = Format

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
  let (height, width, box_num_list) = read_chan (open_in argv.(1)) [] |> read_input in
  F.printf "flag 2\n";
  Puzzle.setup_grid Constraint.solver height width box_num_list;
  F.printf "flag 3\n";
  let status = Z3.Fixedpoint.query Constraint.solver Puzzle.question in
  F.printf "flag 4\n";
  match status with
  | Z3.Solver.SATISFIABLE ->
    F.printf "Can solve\n";
    let answer = Z3.Fixedpoint.get_answer Constraint.solver in
    (match answer with 
    | None -> F.printf "Answer None\n"
    | Some a -> F.printf "%s\n" (a |> Z3.Expr.ast_of_expr |> Z3.AST.to_string))
  | _ ->
    F.printf "Cannot solve\n"

let _ = main Sys.argv
