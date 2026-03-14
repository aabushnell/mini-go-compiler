open Format
open Lib
open Ast
open Tast
open Return_check
open Unused
open Typing_types
open Typing_env
open Typing_validation
open Typing_expr
open Typing_error

(** Function and structure typechecking *)
module DeclTypecheck = struct
  let check_unused_variables func_def typed_body =
    let vars_inside_func = collect_declared_vars typed_body in
    List.iter
      (fun v ->
        if not v.v_used then
          errorm ~loc:v.v_loc "variable %s declared but not used" v.v_name)
      (List.filter
         (fun v -> not (Constants.is_blank v.v_name))
         vars_inside_func)

  let print_function_signature func_def debug =
    if debug then
      printf "function %s : (%s) -> (%s)\n" func_def.fn_name
        (String.concat ", "
           (List.map (fun v -> Types.to_string v.v_typ) func_def.fn_params))
        (String.concat ", " (List.map Types.to_string func_def.fn_typ))

  let function_ struct_env func_env fmt_print_used debug (f : pfunc) :
      function_ * expr =
    Validation.check_no_duplicate_params f;

    let func_def =
      match Hashtbl.find_opt func_env f.pf_name.id with
      | Some def -> def
      | None -> errorm ~loc:f.pf_name.loc "undefined function: %s" f.pf_name.id
    in

    let var_env = VarEnv.empty in
    List.iter (VarEnv.add_var var_env) func_def.fn_params;

    let ctx = make_context struct_env func_env var_env func_def.fn_typ in
    let typed_body = typecheck_expr ctx fmt_print_used f.pf_body in

    if List.length func_def.fn_typ > 0 && not (always_returns typed_body) then
      errorm ~loc:f.pf_name.loc "Not all paths of function: %s return"
        func_def.fn_name;

    check_unused_variables func_def typed_body;
    print_function_signature func_def debug;

    (func_def, typed_body)

  let structure struct_env (s : pstruct) : structure =
    Validation.check_no_duplicate_fields s;

    let fields_list =
      List.map
        (fun (ident, ptyp) ->
          {
            f_name = ident.id;
            f_typ = Types.from_ptyp struct_env ptyp;
            f_ofs = 0;
          })
        s.ps_fields
    in

    let fields_hashtbl = Hashtbl.create (List.length fields_list) in
    List.iter
      (fun field -> Hashtbl.add fields_hashtbl field.f_name field)
      fields_list;

    {
      s_name = s.ps_name.id;
      s_fields = fields_hashtbl;
      s_list = fields_list;
      s_size = 0;
    }

  let declaration struct_env func_env fmt_print_used debug = function
    | PDstruct s -> TDstruct (structure struct_env s)
    | PDfunction f ->
        let func_def, typed_body =
          function_ struct_env func_env fmt_print_used debug f
        in
        TDfunction (func_def, typed_body)
end
