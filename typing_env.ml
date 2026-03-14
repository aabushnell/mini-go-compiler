open Lib
open Ast
open Tast
open Typing_types
open Typing_error

type struct_env = (string, structure) Hashtbl.t
type func_env = (string, function_) Hashtbl.t
type var_list = var list

(** Variable ID generator *)
module VarId = struct
  let counter = ref 0

  let next () =
    incr counter;
    !counter
end

let new_var x loc ty =
  {
    v_name = x;
    v_id = VarId.next ();
    v_loc = loc;
    v_typ = ty;
    v_used = false;
    v_addr = false;
    v_ofs = -1;
  }

(** Variable environment module *)
module VarEnv = struct
  type t = (string, var) Hashtbl.t list

  let empty : t = [ Hashtbl.create 10 ]
  let push_scope (env : t) : t = Hashtbl.create 10 :: env

  let pop_scope (env : t) : t =
    match env with
    | [] -> errorm "cannot pop from empty variable environment"
    | _ :: rest -> rest

  let add_var (env : t) (v : var) : unit =
    match env with
    | [] -> errorm "cannot add variable to empty variable environment"
    | scope :: _ -> Hashtbl.add scope v.v_name v

  let find_current_scope (env : t) (name : string) : var option =
    match env with [] -> None | scope :: _ -> Hashtbl.find_opt scope name

  let rec find_global (env : t) (name : string) : var option =
    match env with
    | [] -> None
    | scope :: rest -> (
        match Hashtbl.find_opt scope name with
        | Some v -> Some v
        | None -> find_global rest name)

  let find_or_error env name loc =
    match find_global env name with
    | Some v -> v
    | None -> errorm ~loc "undefined variable: %s" name

  let check_not_blank v loc =
    if Constants.is_blank v.v_name then
      errorm ~loc "cannot use blank identifier '_' as variable"

  let is_already_declared env name =
    match find_current_scope env name with
    | Some v when not (Constants.is_blank v.v_name) -> true
    | _ -> false
end

(** Environment builder module *)
module EnvBuilder = struct
  let create_empty_struct (s : pstruct) : structure =
    {
      s_name = s.ps_name.id;
      s_fields = Hashtbl.create 10;
      s_list = [];
      s_size = 0;
    }

  let create_field struct_env (fname, ftyp) : field =
    { f_name = fname.id; f_typ = Types.from_ptyp struct_env ftyp; f_ofs = 0 }

  let populate_struct_fields struct_env (s : pstruct) (structure : structure) :
      unit =
    let fields = List.map (create_field struct_env) s.ps_fields in
    List.iter
      (fun field -> Hashtbl.add structure.s_fields field.f_name field)
      fields;
    structure.s_list <- fields

  let build_struct_env (structs : pstruct list) ~debug : struct_env =
    let struct_env = Hashtbl.create (List.length structs) in

    (* Add empty structures first *)
    List.iter
      (fun s -> Hashtbl.add struct_env s.ps_name.id (create_empty_struct s))
      structs;

    (* Populate fields *)
    List.iter
      (fun s ->
        let structure = Hashtbl.find struct_env s.ps_name.id in
        populate_struct_fields struct_env s structure)
      structs;

    if debug then
      Hashtbl.iter
        (fun name _ -> Printf.printf "known structure: %s\n" name)
        struct_env;

    struct_env

  let create_param struct_env (ident, ptyp) : var =
    let param_type = Types.from_ptyp struct_env ptyp in
    new_var ident.id ident.loc param_type

  let create_function struct_env (f : pfunc) : function_ =
    {
      fn_name = f.pf_name.id;
      fn_params = List.map (create_param struct_env) f.pf_params;
      fn_typ = List.map (Types.from_ptyp struct_env) f.pf_typ;
    }

  let add_builtin_functions func_env =
    Hashtbl.add func_env Constants.fmt_print
      { fn_name = Constants.fmt_print; fn_params = []; fn_typ = [] }

  let build_func_env (struct_env : struct_env) (funcs : pfunc list)
      (has_import : bool) : func_env =
    let func_env = Hashtbl.create (List.length funcs) in

    (* Add user-defined functions *)
    List.iter
      (fun f ->
        Hashtbl.add func_env f.pf_name.id (create_function struct_env f))
      funcs;

    (* Add builtin functions *)
    if has_import then add_builtin_functions func_env;

    func_env
end

type typing_context = {
  structs : struct_env;
  funcs : func_env;
  vars : VarEnv.t;
  expected_return : typ list;
}
(** Typing context containing all environments and expected return types *)

let make_context structs funcs vars expected_return =
  { structs; funcs; vars; expected_return }

let push_scope_ctx ctx = { ctx with vars = VarEnv.push_scope ctx.vars }