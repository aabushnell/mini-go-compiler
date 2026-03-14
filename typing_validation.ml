open Lib
open Ast
open Tast
open Graph
open Typing_types
open Typing_env
open Typing_error
open Utils

(** Arity and type matching utilities *)
module ArityChecker = struct
  (** Unpack Tmany if needed and verify arity *)
  let unpack_and_check ~loc ~expected_count ~actual_types ~context =
    match actual_types with
    | [ Tmany types ] when expected_count > 1 ->
        if List.length types <> expected_count then
          errorm ~loc "%s arity mismatch: expected %d, got %d" 
            context expected_count (List.length types);
        types
    | types when List.length types = expected_count -> types
    | types ->
        errorm ~loc "%s arity mismatch: expected %d, got %d" 
          context expected_count (List.length types)

  (** Check types match between two lists *)
  let check_type_match ~loc ~expected ~actual ~context =
    List.iter2
      (fun exp act ->
        if not (Types.equal exp act) then
          errorm ~loc "%s type mismatch: expected %s, got %s" 
            context (Types.to_string exp) (Types.to_string act))
      expected actual

  (** Check single type matches *)
  let check_single ~loc ~expected ~actual ~context =
    if not (Types.equal expected actual) then
      errorm ~loc "%s type mismatch: expected %s, got %s" 
        context (Types.to_string expected) (Types.to_string actual)
end

(** Validation module for checking duplicates and cycles *)
module Validation = struct
  let check_no_duplicate_functions (funcs : pfunc list) : unit =
    check_duplicates
      ~get_key:(fun (ident, _typ) -> ident.id)
      ~on_duplicate:(fun (ident, _typ) ->
        errorm ~loc:ident.loc "duplicate function: %s" ident.id)
      (List.filter_map (fun f -> Some (f.pf_name, f.pf_typ)) funcs)

  let check_no_duplicate_structs (structs : pstruct list) : unit =
    check_duplicates
      ~get_key:(fun ident -> ident.id)
      ~on_duplicate:(fun ident ->
        errorm ~loc:ident.loc "duplicate structure: %s" ident.id)
      (List.filter_map (fun s -> Some s.ps_name) structs)

  let check_no_duplicate_fields (s : pstruct) : unit =
    check_duplicates
      ~get_key:(fun (ident, _typ) -> ident.id)
      ~on_duplicate:(fun (ident, _typ) ->
        errorm ~loc:ident.loc "duplicate field: %s for structure: %s" 
          ident.id s.ps_name.id)
      s.ps_fields

  let check_no_duplicate_params (f : pfunc) : unit =
    check_duplicates
      ~get_key:(fun (ident, _typ) -> ident.id)
      ~on_duplicate:(fun (ident, _typ) ->
        errorm ~loc:ident.loc "duplicate parameter: %s for function: %s"
          ident.id f.pf_name.id)
      f.pf_params

  let check_struct_cycles (structs : pstruct list) : unit =
    let dep_graph = build_graph structs in
    let cycles = detect_cycles structs dep_graph in
    if cycles <> [] then
      errorm "Found following cycles in the structures declarations:\n%s"
        (String.concat "\n" cycles)

  let check_main_signature (func_env : func_env) : unit =
    match Hashtbl.find_opt func_env Constants.main_function with
    | Some main_func ->
        if List.length main_func.fn_params <> 0 then
          errorm "function main must not have parameters, got %d"
            (List.length main_func.fn_params);
        if List.length main_func.fn_typ <> 0 then
          errorm "function main must not have return values, got %d"
            (List.length main_func.fn_typ)
    | None -> errorm "function main is not defined"

  let check_fmt_import_used (has_import : bool) (fmt_print_used : bool) : unit =
    if has_import && not fmt_print_used then
      errorm "imported package fmt is not used"
end