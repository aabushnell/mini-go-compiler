open Format
open Lib
open Ast
open Tast
open Typing_types
open Typing_env
open Typing_validation
open Typing_decl
open Typing_error

(** Configuration *)
let debug = ref false
let fmt_print_used = ref false

(** Main file typechecking *)
let separate_declarations dl =
  let structs =
    List.filter_map (function PDstruct s -> Some s | _ -> None) dl
  in
  let functions =
    List.filter_map (function PDfunction f -> Some f | _ -> None) dl
  in
  (structs, functions)

let file ~debug:b ((imp, dl) : Ast.pfile) : Tast.tfile =
  debug := b;
  fmt_print_used := false;

  let list_of_structs, list_of_functions = separate_declarations dl in

  (* Validate: check for duplicates *)
  Validation.check_no_duplicate_functions list_of_functions;
  Validation.check_no_duplicate_structs list_of_structs;

  (* Build environments *)
  let struct_env = EnvBuilder.build_struct_env list_of_structs ~debug:!debug in
  Validation.check_struct_cycles list_of_structs;

  let func_env = EnvBuilder.build_func_env struct_env list_of_functions imp in

  (* Typecheck all declarations *)
  let typed_decls =
    List.map (DeclTypecheck.declaration struct_env func_env fmt_print_used !debug) dl
  in

  (* Final validations *)
  Validation.check_fmt_import_used imp !fmt_print_used;
  Validation.check_main_signature func_env;

  typed_decls