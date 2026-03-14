open Lib
open Ast
open Tast
open Typing_error

(** Type operations module *)
module Types = struct
  let builtin_of_string = function
    | "int" -> Some Tint
    | "bool" -> Some Tbool
    | "string" -> Some Tstring
    | _ -> None

  let rec from_ptyp (struct_env : (string, structure) Hashtbl.t) (pt : ptyp) : typ =
    match pt with
    | PTident id -> (
        match builtin_of_string id.id with
        | Some t -> t
        | None -> (
            match Hashtbl.find_opt struct_env id.id with
            | Some s -> Tstruct s
            | None ->
                errorm ~loc:id.loc "undefined structure: %s used as a type" id.id))
    | PTptr pt' -> Tptr (from_ptyp struct_env pt')

  let to_string = Utils.string_of_typ
  let equal = Utils.types_equal
  let is_nil = function Tnil -> true | _ -> false
  let is_pointer = function Tptr _ -> true | _ -> false
  let is_struct = function Tstruct _ -> true | _ -> false
end

(** Result type construction utilities *)
module ResultType = struct
  let make = function [] -> Tmany [] | [ t ] -> t | ts -> Tmany ts
  let empty = Tmany []
end

(** Constants used throughout the typechecker *)
module Constants = struct
  let builtin_types = [ "int"; "bool"; "string" ]
  let blank_identifier = "_"
  let main_function = "main"
  let new_keyword = "new"
  let fmt_print = "fmt.Print"
  let is_blank name = name = blank_identifier
  let is_builtin_type name = List.mem name builtin_types
end