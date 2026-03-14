open Ast
module StringSet = Set.Make (String)

let get_struct_dependencies (s : pstruct) : StringSet.t =
  List.fold_left
    (fun acc (f_ident, f_type) ->
      match f_type with
      | PTident id when id.id <> "int" && id.id <> "bool" && id.id <> "string"
        ->
          StringSet.add id.id acc
      | _ -> acc)
    StringSet.empty s.ps_fields

let build_graph (structs : pstruct list) : (string, StringSet.t) Hashtbl.t =
  let graph = Hashtbl.create (List.length structs) in
  List.iter
    (fun s ->
      let deps = get_struct_dependencies s in
      Hashtbl.add graph s.ps_name.id deps)
    structs;

  graph

let detect_cycles (structs : pstruct list)
    (graph : (string, StringSet.t) Hashtbl.t) : string list =
  let visited = ref StringSet.empty in
  let cycles = ref [] in

  let rec dfs s_name path =
    if StringSet.mem s_name !visited then
      cycles := String.concat " -> " (List.rev (s_name :: path)) :: !cycles
    else begin
      visited := StringSet.add s_name !visited;

      match Hashtbl.find_opt graph s_name with
      | Some neighbors ->
          StringSet.iter (fun n -> dfs n (s_name :: path)) neighbors
      | None -> ()
    end
  in

  (* iterate over all structs *)
  List.iter
    (fun s ->
      dfs s.ps_name.id [];
      visited := StringSet.empty)
    structs;

  !cycles
