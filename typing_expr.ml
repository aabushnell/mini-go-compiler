open Format
open Lib
open Ast
open Tast
open Typing_types
open Typing_env
open Typing_validation
open Typing_error

(** Operator type checking *)
module OperatorChecker = struct
  let check_binop ~loc op t1 t2 =
    match op with
    | Badd | Bsub | Bmul | Bdiv | Bmod ->
        if t1 = Tint && t2 = Tint then Tint
        else
          errorm ~loc "operator %s requires two integers%s, got %s and %s"
            (Utils.string_of_binop op)
            (if op = Badd then " (or two strings)" else "")
            (Types.to_string t1) (Types.to_string t2)
    | Blt | Ble | Bgt | Bge ->
        if t1 = Tint && t2 = Tint then Tbool
        else
          errorm ~loc "operator %s requires two integers, got %s and %s"
            (Utils.string_of_binop op) (Types.to_string t1) (Types.to_string t2)
    | Beq | Bne ->
        if Types.equal t1 t2 && not (t1 = Tnil && t2 = Tnil) then Tbool
        else
          errorm ~loc "operator %s requires compatible types, got %s and %s"
            (Utils.string_of_binop op) (Types.to_string t1) (Types.to_string t2)
    | Band | Bor ->
        if t1 = Tbool && t2 = Tbool then Tbool
        else
          errorm ~loc "operator %s requires two booleans, got %s and %s"
            (Utils.string_of_binop op) (Types.to_string t1) (Types.to_string t2)

  let check_unop_simple ~loc op t =
    match op with
    | Uneg when t = Tint -> Tint
    | Uneg -> errorm ~loc "unary - requires int, got %s" (Types.to_string t)
    | Unot when t = Tbool -> Tbool
    | Unot -> errorm ~loc "unary ! requires bool, got %s" (Types.to_string t)
    | _ -> failwith "use check_address or check_deref for & and *"
end

(** Structure field access utilities *)
module StructAccess = struct
  (** Extract struct from type, handling auto-dereference *)
  let extract_struct ~loc typ =
    match typ with
    | Tstruct s -> s
    | Tptr (Tstruct s) -> s (* auto-dereference *)
    | Tnil -> errorm ~loc "cannot access field of nil (type unknown)"
    | t ->
        errorm ~loc "cannot access field of non-structure type %s"
          (Types.to_string t)

  (** Find field in structure *)
  let find_field ~loc struct_type field_name =
    match Hashtbl.find_opt struct_type.s_fields field_name with
    | Some field -> field
    | None ->
        errorm ~loc "structure %s has no field named %s" struct_type.s_name
          field_name
end

(** Expression analysis utilities *)
module ExprAnalysis = struct
  let is_lvalue (e : pexpr) : bool =
    match e.pexpr_desc with
    | PEident _ | PEdot _ | PEunop _ -> true
    | _ -> false

  let require_lvalue ~loc e =
    if not (is_lvalue e) then errorm ~loc "expression must be an lvalue"

  let require_type ~loc expected actual context =
    ArityChecker.check_single ~loc ~expected ~actual ~context

  (** Mark variables as having their address taken *)
  let rec mark_address_taken = function
    | TEident v -> v.v_addr <- true
    | TEdot (base_expr, _) -> mark_address_taken base_expr.expr_desc
    | _ -> ()
end

(** Type checking for individual expression types *)
module ExprTypecheck = struct
  let skip () : expr = { expr_desc = TEskip; expr_typ = ResultType.empty }

  let constant (c : constant) : expr =
    let typ =
      match c with Cbool _ -> Tbool | Cint _ -> Tint | Cstring _ -> Tstring
    in
    { expr_desc = TEconstant c; expr_typ = typ }

  let binop (typecheck_rec : pexpr -> expr) op e1 e2 loc : expr =
    let te1 = typecheck_rec e1 in
    let te2 = typecheck_rec e2 in
    let result_type =
      OperatorChecker.check_binop ~loc op te1.expr_typ te2.expr_typ
    in
    { expr_desc = TEbinop (op, te1, te2); expr_typ = result_type }

  let unop_address ~loc te t e =
    (* Check lvalue only for address-of operator *)
    ExprAnalysis.require_lvalue ~loc e;
    if t = Tnil then errorm ~loc "cannot take address of nil";
    ExprAnalysis.mark_address_taken te.expr_desc;
    Tptr t

  let unop_deref ~loc t =
    match t with
    | Tptr t -> t
    | Tnil -> errorm ~loc "cannot dereference nil (type unknown)"
    | _ ->
        errorm ~loc "cannot dereference non-pointer type %s" (Types.to_string t)

  let unop (typecheck_rec : pexpr -> expr) op e loc : expr =
    (* Don't check lvalue here - only address-of needs it *)
    let te = typecheck_rec e in
    let t = te.expr_typ in
    let result_type =
      match op with
      | Uneg | Unot -> OperatorChecker.check_unop_simple ~loc op t
      | Uamp -> unop_address ~loc te t e (* lvalue check is inside *)
      | Ustar -> unop_deref ~loc t
    in
    { expr_desc = TEunop (op, te); expr_typ = result_type }

  let nil () : expr = { expr_desc = TEnil; expr_typ = Tnil }

  let new_expr ctx pexpr_list loc =
    if List.length pexpr_list <> 1 then
      errorm ~loc "new expects exactly 1 argument, got %d"
        (List.length pexpr_list);
    match (List.hd pexpr_list).pexpr_desc with
    | PEident type_ident -> (
        match Hashtbl.find_opt ctx.structs type_ident.id with
        | Some s ->
            { expr_desc = TEnew (Tstruct s); expr_typ = Tptr (Tstruct s) }
        | None -> errorm ~loc:type_ident.loc "undefined type: %s" type_ident.id)
    | _ -> errorm ~loc "new expects a type name as argument"

  let fmt_print typecheck_rec pexpr_list fmt_print_used =
    fmt_print_used := true;
    List.map typecheck_rec pexpr_list

  let regular_call ~loc func_def typed_args =
    let arg_types = List.map (fun te -> te.expr_typ) typed_args in
    let actual_types =
      ArityChecker.unpack_and_check ~loc
        ~expected_count:(List.length func_def.fn_params)
        ~actual_types:arg_types
        ~context:("function " ^ func_def.fn_name)
    in
    ArityChecker.check_type_match ~loc
      ~expected:(List.map (fun v -> v.v_typ) func_def.fn_params)
      ~actual:actual_types
      ~context:("function " ^ func_def.fn_name ^ " argument");
    typed_args

  let call ctx typecheck_rec ident pexpr_list loc fmt_print_used : expr =
    if ident.id = Constants.new_keyword then new_expr ctx pexpr_list ident.loc
    else
      match Hashtbl.find_opt ctx.funcs ident.id with
      | None -> errorm ~loc:ident.loc "undefined function: %s" ident.id
      | Some func_def ->
          let typed_args = List.map typecheck_rec pexpr_list in
          if ident.id = Constants.fmt_print then
            {
              expr_desc =
                TEprint (fmt_print typecheck_rec pexpr_list fmt_print_used);
              expr_typ = ResultType.empty;
            }
          else
            let final_args = regular_call ~loc:ident.loc func_def typed_args in
            {
              expr_desc = TEcall (func_def, final_args);
              expr_typ = ResultType.make func_def.fn_typ;
            }

  let ident ctx ident : expr =
    let v = VarEnv.find_or_error ctx.vars ident.id ident.loc in
    VarEnv.check_not_blank v ident.loc;
    v.v_used <- true;
    { expr_desc = TEident v; expr_typ = v.v_typ }

  let dot typecheck_rec base_expr field_ident : expr =
    let tbase_expr = typecheck_rec base_expr in
    let struct_type =
      StructAccess.extract_struct ~loc:base_expr.pexpr_loc tbase_expr.expr_typ
    in
    let field =
      StructAccess.find_field ~loc:field_ident.loc struct_type field_ident.id
    in
    { expr_desc = TEdot (tbase_expr, field); expr_typ = field.f_typ }

  let assign typecheck_rec lhs_list rhs_list loc : expr =
    List.iter (ExprAnalysis.require_lvalue ~loc) lhs_list;

    let t_lhs_list = List.map typecheck_rec lhs_list in
    let t_rhs_list = List.map typecheck_rec rhs_list in

    let lhs_types = List.map (fun l -> l.expr_typ) t_lhs_list in
    let rhs_types = List.map (fun r -> r.expr_typ) t_rhs_list in

    let unpacked_rhs_types =
      ArityChecker.unpack_and_check ~loc ~expected_count:(List.length lhs_list)
        ~actual_types:rhs_types ~context:"assignment"
    in

    ArityChecker.check_type_match ~loc ~expected:lhs_types
      ~actual:unpacked_rhs_types ~context:"assignment";

    {
      expr_desc = TEassign (t_lhs_list, t_rhs_list);
      expr_typ = ResultType.empty;
    }

  let deduce_var_types ctx loc ident_list opt_typ init_types =
    match opt_typ with
    | Some ptyp ->
        let typ = Types.from_ptyp ctx.structs ptyp in
        (* Only check if we have init expressions *)
        if List.length init_types > 0 then
          ArityChecker.check_type_match ~loc
            ~expected:(List.map (fun _ -> typ) ident_list)
            ~actual:init_types ~context:"variable declaration";
        List.map (fun _ -> typ) ident_list
    | None ->
        (* Without type annotation, we must have init expressions *)
        if List.length init_types = 0 then
          errorm ~loc
            "variable declaration requires either type annotation or \
             initialization";
        if List.exists Types.is_nil init_types then
          errorm ~loc "cannot deduce type from nil initial value";
        init_types

  let create_or_reuse_var ctx ident deduced_type =
    (* Check if this identifier is the blank identifier *)
    if Constants.is_blank ident.id then (
      (* Blank identifier: always create a new variable, never error *)
      let v = new_var ident.id ident.loc deduced_type in
      VarEnv.add_var ctx.vars v;
      v)
    else
      (* Regular identifier: check for redeclaration in current scope only *)
      match VarEnv.find_current_scope ctx.vars ident.id with
      | Some _ ->
          (* Already declared in current scope - this is an error *)
          errorm ~loc:ident.loc "variable %s already declared" ident.id
      | None ->
          (* Not in current scope - OK to declare (may shadow outer scope) *)
          let v = new_var ident.id ident.loc deduced_type in
          VarEnv.add_var ctx.vars v;
          v

  let vars ctx typecheck_rec ident_list opt_typ init_exprs loc : expr =
    let init_types =
      List.map (fun expr -> (typecheck_rec expr).expr_typ) init_exprs
    in

    (* Only unpack and check arity if we have init expressions *)
    let unpacked_init_types =
      if List.length init_types > 0 then
        ArityChecker.unpack_and_check ~loc
          ~expected_count:(List.length ident_list) ~actual_types:init_types
          ~context:"variable declaration"
      else []
    in

    let deduced_types =
      deduce_var_types ctx loc ident_list opt_typ unpacked_init_types
    in

    let created_variables =
      List.map2 (create_or_reuse_var ctx) ident_list deduced_types
    in
    { expr_desc = TEvars created_variables; expr_typ = ResultType.empty }

  let if_expr typecheck_rec cond then_branch else_branch cond_loc : expr =
    let cond_typed = typecheck_rec cond in
    ExprAnalysis.require_type ~loc:cond_loc Tbool cond_typed.expr_typ
      "if condition";
    let then_typed = typecheck_rec then_branch in
    let else_typed = typecheck_rec else_branch in
    {
      expr_desc = TEif (cond_typed, then_typed, else_typed);
      expr_typ = ResultType.empty;
    }

  let return ctx typecheck_rec exprs loc : expr =
    let typed_exprs = List.map typecheck_rec exprs in
    let return_types = List.map (fun te -> te.expr_typ) typed_exprs in

    let unpacked_return_types =
      ArityChecker.unpack_and_check ~loc
        ~expected_count:(List.length ctx.expected_return)
        ~actual_types:return_types ~context:"return"
    in

    ArityChecker.check_type_match ~loc ~expected:ctx.expected_return
      ~actual:unpacked_return_types ~context:"return";

    { expr_desc = TEreturn typed_exprs; expr_typ = ResultType.empty }

  let block typecheck_fn ctx exprs : expr =
    let ctx' = push_scope_ctx ctx in
    let typed_exprs = List.map (typecheck_fn ctx') exprs in
    { expr_desc = TEblock typed_exprs; expr_typ = ResultType.empty }

  let for_loop typecheck_fn ctx cond block cond_loc : expr =
    let ctx' = push_scope_ctx ctx in
    let cond_typed = typecheck_fn ctx' cond in
    ExprAnalysis.require_type ~loc:cond_loc Tbool cond_typed.expr_typ
      "for condition";
    let block_typed = typecheck_fn ctx' block in
    { expr_desc = TEfor (cond_typed, block_typed); expr_typ = ResultType.empty }

  let incdec typecheck_rec expr incdec loc : expr =
    ExprAnalysis.require_lvalue ~loc expr;
    let t_expr = typecheck_rec expr in
    ExprAnalysis.require_type ~loc Tint t_expr.expr_typ "increment/decrement";
    { expr_desc = TEincdec (t_expr, incdec); expr_typ = Tint }
end

(** Main recursive type checking function for expressions *)
let rec typecheck_expr (ctx : typing_context) (fmt_print_used : bool ref)
    (e : pexpr) : expr =
  let typecheck_rec = typecheck_expr ctx fmt_print_used in

  match e.pexpr_desc with
  | PEskip -> ExprTypecheck.skip ()
  | PEconstant c -> ExprTypecheck.constant c
  | PEbinop (op, e1, e2) ->
      ExprTypecheck.binop typecheck_rec op e1 e2 e.pexpr_loc
  | PEunop (op, e1) -> ExprTypecheck.unop typecheck_rec op e1 e.pexpr_loc
  | PEnil -> ExprTypecheck.nil ()
  | PEcall (ident, pexpr_list) ->
      ExprTypecheck.call ctx typecheck_rec ident pexpr_list e.pexpr_loc
        fmt_print_used
  | PEident ident -> ExprTypecheck.ident ctx ident
  | PEdot (base_expr, field_ident) ->
      ExprTypecheck.dot typecheck_rec base_expr field_ident
  | PEassign (lhs_list, rhs_list) ->
      ExprTypecheck.assign typecheck_rec lhs_list rhs_list e.pexpr_loc
  | PEvars (ident_list, opt_typ, init_exprs) ->
      ExprTypecheck.vars ctx typecheck_rec ident_list opt_typ init_exprs
        e.pexpr_loc
  | PEif (cond, then_branch, else_branch) ->
      ExprTypecheck.if_expr typecheck_rec cond then_branch else_branch
        cond.pexpr_loc
  | PEreturn exprs -> ExprTypecheck.return ctx typecheck_rec exprs e.pexpr_loc
  | PEblock exprs ->
      ExprTypecheck.block
        (fun ctx -> typecheck_expr ctx fmt_print_used)
        ctx exprs
  | PEfor (cond, block) ->
      ExprTypecheck.for_loop
        (fun ctx -> typecheck_expr ctx fmt_print_used)
        ctx cond block cond.pexpr_loc
  | PEincdec (expr, incdec) ->
      ExprTypecheck.incdec typecheck_rec expr incdec expr.pexpr_loc
