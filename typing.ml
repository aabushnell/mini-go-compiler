
(** Static type checking of Mini Go programs *)

open Format
open Lib
open Ast
open Tast

let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

module Config = struct
  type sizes = {
    structs : int;
    funcs : int;
    locals : int;
    seen_ids : int;
  }

  let table_sizes = {
    structs = 64;
    funcs = 64;
    locals = 256;
    seen_ids = 64;
  }
end

type env = {
  structs : (string, structure) Hashtbl.t;
  funcs   : (string, function_) Hashtbl.t;
}

type func_env = {
  genv     : env;
  scope    : (string, var) Hashtbl.t;
  local    : (string, unit) Hashtbl.t;
  rtypes   : typ list;
  printed  : bool ref;
}

type expr_res = {
  texpr   : Tast.expr;
  returns : bool;
  lvalue  : bool;
}

let mk_result ?(returns=false) ?(lvalue=false) texpr : expr_res =
  { texpr; returns; lvalue }

exception Error of Ast.location * string

(** use this function to report errors; it is a printf-like function, eg.

    errorm ~loc "bad arity %d for function %s" n f

*)
let errorm ?(loc=dummy_loc) f =
Format.kasprintf (fun s -> raise (Error (loc, s))) ("@[" ^^ f ^^ "@]")

(** use this function to create variable, so that they all have a
    unique id if field `v_id` *)
let new_var : string -> Ast.location -> typ -> var =
  let id = ref 0 in
  fun x loc ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty;
      v_used = false; v_addr = false; v_ofs= -1 }

let rec equal_typ typ1 typ2 =
  match typ1, typ2 with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tnil, Tptr _ | Tptr _, Tnil -> true
  | Tnil, Tnil -> true
  | Tptr u1, Tptr u2 -> equal_typ u1 u2
  | Tmany l1, Tmany l2 ->
      List.length l1 = List.length l2 &&
      List.for_all2 equal_typ l1 l2
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | _ -> false

let rec form_type (structs: (string, structure) Hashtbl.t) (pt: ptyp) : typ =
  match pt with
  | PTident id ->
      begin match id.id with
      | "int"    -> Tint
      | "bool"   -> Tbool
      | "string" -> Tstring
      | s ->
          if Hashtbl.mem structs s then
            Tstruct (Hashtbl.find structs s)
          else
            errorm ~loc:id.loc "Unknown type: %s" s
      end
  | PTptr t -> Tptr (form_type structs t)

let check_rec_struct loc (start : structure) : unit =
  let rec dfs depth path (s : structure) =
    if depth > 10 then
      failwith "Possible infinite recursion in check_rec_structs";
    if List.memq s path then
      errorm ~loc "Recursive structure definition involving %s" s.s_name;

    Hashtbl.iter (fun _ (f : field) ->
      match f.f_typ with
      | Tstruct s' -> dfs (depth + 1) (s :: path) s'
      | _ -> ()
    ) s.s_fields
  in
  dfs 0 [] start

let rec form_expr (fenv: func_env) (e: Ast.pexpr) : expr_res =
  let loc = e.pexpr_loc in
  match e.pexpr_desc with
  | PEskip ->
      let texpr = { expr_desc = TEskip; expr_typ = Tmany [] } in
      mk_result texpr
  | PEconstant c ->
      let typ =
        match c with
        | Cbool _   -> Tbool
        | Cint _    -> Tint
        | Cstring _ -> Tstring
      in
      let texpr = { expr_desc = TEconstant c; expr_typ = typ } in
      mk_result texpr
  | PEbinop (op, pexpr1, pexpr2) ->
      let res1 = form_expr fenv pexpr1 in
      let typ1 = res1.texpr.expr_typ in
      let res2 = form_expr fenv pexpr2 in
      let typ2 = res2.texpr.expr_typ in
      let op_typ =
        match op with
        | Badd | Bsub | Bmul | Bdiv | Bmod ->
            if (not (equal_typ typ1 Tint)) || (not (equal_typ typ2 Tint)) then
              errorm ~loc:e.pexpr_loc "Arithmetic op expects int operands";
            Tint
        | Blt | Ble | Bgt | Bge ->
            if (not (equal_typ typ1 Tint)) || (not (equal_typ typ2 Tint)) then
              errorm ~loc:e.pexpr_loc "Comparison op expects int operands";
            Tbool
        | Band | Bor ->
            if (not (equal_typ typ1 Tbool)) || (not (equal_typ typ2 Tbool)) then
              errorm ~loc:e.pexpr_loc "Logical op expects int operands";
            Tbool
        | Beq | Bne ->
            if (typ1 = Tnil) && (typ2 = Tnil) then
              errorm ~loc:e.pexpr_loc "Cannot compare nil with nil";
            let types_match =
              (equal_typ typ1 typ2) ||
              ((equal_typ typ1 Tnil) && (match typ2 with
                            | Tptr _ -> true
                            | _ -> false)) ||
              ((equal_typ typ2 Tnil) && (match typ1 with
                            | Tptr _ -> true
                            | _ -> false))
            in
            if not types_match then
              errorm ~loc:e.pexpr_loc "Invalid ==/!= operand types";
            Tbool
      in
      let texpr = { expr_desc = TEbinop (op, res1.texpr, res2.texpr); expr_typ = op_typ } in
      mk_result texpr
  | PEunop (op, pexpr) ->
      let res = form_expr fenv pexpr in
      let typ = res.texpr.expr_typ in
      let (op_typ, lval) =
        match op with
        | Uneg ->
            if not (equal_typ typ Tint) then
              errorm ~loc:e.pexpr_loc "Unary - expects int";
            (Tint, false)
        | Unot ->
            if not (equal_typ typ Tbool) then
              errorm ~loc:e.pexpr_loc "Unary ! expects bool";
            (Tbool, false)
        | Uamp ->
            if not res.lvalue then
              errorm ~loc:e.pexpr_loc "Can only take address of an l-value";
            begin match res.texpr.expr_desc with
            | TEident v -> v.v_addr <- true
            | _ -> ()
            end;
            (Tptr typ, false)
        | Ustar ->
            let pt_typ =
              match typ with
              | Tptr t' -> t'
              | Tnil ->
                errorm ~loc:e.pexpr_loc "Cannot dereference null pointer"
              | _ ->
                errorm ~loc:e.pexpr_loc "Cannot dereference non-pointer expression"
            in
            (pt_typ, true)
      in
      let texpr = { expr_desc = TEunop (op, res.texpr); expr_typ = op_typ } in
      mk_result ~lvalue:lval texpr
  | PEnil ->
      let texpr = { expr_desc = TEnil; expr_typ = Tnil } in
      mk_result texpr
  | PEcall (id, pargs) ->
      let (desc, typ) =
        match id.id with
        | "new" ->
            begin match pargs with
            | [] -> errorm ~loc:id.loc "new() requires a type argument"
            | [pexpr] ->
                begin match pexpr.pexpr_desc with
                | PEident {id; loc} ->
                    let s =
                      try Hashtbl.find fenv.genv.structs id
                      with Not_found -> errorm ~loc "Unknown type %s" id
                    in
                    let s_typ = Tstruct s in
                    (TEnew s_typ, Tptr s_typ)
                | _ ->
                    errorm ~loc:id.loc "new() requires a type name, not an expression"
                end
            | _ ->
                errorm ~loc:id.loc "new() takes exactly one type argument"
            end
        | _ ->

          let args =
            List.map (fun pexpr ->
              let res = form_expr fenv pexpr in
              res.texpr
            ) pargs
          in

          let arg_typs =
            match args with
            | [{expr_desc=TEcall(inner_fn, _); _}]
              when List.length inner_fn.fn_typ > 1 ->
                inner_fn.fn_typ
            | _ ->
                List.map (fun e -> e.expr_typ) args
          in

          match id.id with
          | "fmt.Print" ->
            fenv.printed := true;
            List.iter (fun typ ->
              match typ with
              | Tint | Tbool | Tstring | Tnil -> ()
              | Tptr _ -> ()
              | _ ->
                  errorm ~loc:id.loc
                    "Cannot print values of type %a"
                    Pretty.typ typ
            ) arg_typs;
            (TEprint args, Tmany [])
          | _ ->
            let fn =
              try Hashtbl.find fenv.genv.funcs id.id
              with Not_found -> errorm ~loc:id.loc "Unknown function %s" id.id
            in

            if List.length arg_typs <> List.length fn.fn_params then
              errorm ~loc:id.loc
                "Function %s expects %d arguments but got %d"
                id.id (List.length fn.fn_params) (List.length arg_typs);

            List.iter2 (fun typ param ->
              if not (equal_typ typ param.v_typ) then
                errorm ~loc:id.loc "Type mismatch in argument"
            ) arg_typs fn.fn_params;

            let fn_typ =
              match fn.fn_typ with
              | []  -> Tmany []
              | [t] -> t
              | l   -> Tmany l
            in
            (TEcall (fn, args), fn_typ)
      in
      let texpr = { expr_desc = desc; expr_typ = typ } in
      mk_result texpr
  | PEident id ->
      if id.id = "_" then
        errorm ~loc:id.loc "Cannot use _ as a value";
      let var =
        try Hashtbl.find fenv.scope id.id
        with Not_found -> errorm ~loc:id.loc "Unbound variable %s" id.id
      in
      var.v_used <- true;
      let texpr = { expr_desc = TEident var; expr_typ = var.v_typ } in
      mk_result ~lvalue:true texpr
  | PEdot (pexpr, id) ->
      let res = form_expr fenv pexpr in
      let typ = res.texpr.expr_typ in
      let (s, ptr) =
        match typ with
        | Tstruct s -> (s, false)
        | Tptr (Tstruct s) -> (s, true)
        | _ ->
            errorm ~loc "Dot selection on non-struct type"
      in
      let field =
        try Hashtbl.find s.s_fields id.id
        with Not_found ->
          errorm ~loc:id.loc "Unknown field %s in struct %s" id.id s.s_name
      in
      let texpr = { expr_desc = TEdot (res.texpr, field); expr_typ = field.f_typ } in
      mk_result ~lvalue:true texpr
  | PEassign (lhs, rhs) ->
      let lhs_exprs =
        List.map (fun pexpr ->
          let res = form_expr fenv pexpr in
          if not res.lvalue then
            errorm ~loc:pexpr.pexpr_loc "Left-hand side is not assignable";
          res.texpr
        ) lhs
      in
      let lhs_typs =
        List.map (fun expr ->
          expr.expr_typ
        ) lhs_exprs
      in

      let rhs_exprs =
        List.map (fun pexpr ->
          let res = form_expr fenv pexpr in
          res.texpr
        ) rhs
      in
      let rhs_typs =
        match rhs_exprs with
        | [expr] ->
            begin match expr.expr_typ with
            | Tmany typs ->
                typs
            | typ ->
                [typ]
            end
        | _ ->
            List.map (fun expr -> expr.expr_typ) rhs_exprs
      in

      let n_lhs = List.length lhs_typs in
      let n_rhs = List.length rhs_typs in
      if n_lhs <> n_rhs then
        errorm ~loc "Number of variables does not match number of assigned values";
      List.iter2 (fun ltyp rtyp ->
        if not (equal_typ ltyp rtyp) then
          errorm ~loc "Type mismatch in assignment"
      ) lhs_typs rhs_typs;

      let texpr = { expr_desc = TEassign (lhs_exprs, rhs_exprs); expr_typ = Tmany [] } in
      mk_result texpr
  | PEvars (ids, pt_op, inits) ->
      let n_ids = List.length ids in
      let n_inits = List.length inits in

      let (var_typs, typed_inits) =
        match pt_op, inits with
        (* var x1,...,xn τ; *)
        | Some pt, [] ->
            let t = form_type fenv.genv.structs pt in
            (List.init n_ids (fun _ -> t), [])
        (* var x1,...,xn τ = e;  or  var x1,...,xn τ = f(...); *)
        | Some pt, [e] ->
            let t = form_type fenv.genv.structs pt in
            begin match e.pexpr_desc with
            | PEcall (id, _) when n_ids > 1 ->
                let fn =
                  try Hashtbl.find fenv.genv.funcs id.id
                  with Not_found -> errorm ~loc:id.loc "Unknown function %s" id.id
                in
                if List.length fn.fn_typ <> n_ids then
                  errorm ~loc "Number of variables does not match number of initializations";
                List.iter (fun rt ->
                  if not (equal_typ rt t) then
                    errorm ~loc "Return type does not match declared type"
                ) fn.fn_typ;
                let res = form_expr fenv e in
                (List.init n_ids (fun _ -> t), [res.texpr])
            | _ ->
                if n_ids <> 1 then
                  errorm ~loc "Number of variables does not match number of initializations";
                let res = form_expr fenv e in
                if not (equal_typ res.texpr.expr_typ t) then
                  errorm ~loc "Initializer type mismatch in var declaration";
                ([t], [res.texpr])
            end
        (* var x1,...,xn τ = e1,...,en;  (n>=2) *)
        | Some pt, _ when n_inits = n_ids ->
            let t = form_type fenv.genv.structs pt in
            let rinits = List.map (form_expr fenv) inits in
            List.iter (fun r ->
              if not (equal_typ r.texpr.expr_typ t) then
                errorm ~loc "Initializer type mismatch in var declaration"
            ) rinits;
            (List.init n_ids (fun _ -> t), List.map (fun r -> r.texpr) rinits)
        (* var x1,...,xn = e;  or  var x1,...,xn = f(...); *)
        | None, [e] ->
            begin match e.pexpr_desc with
            | PEcall (id, _) when n_ids > 1 ->
                let fn =
                  try Hashtbl.find fenv.genv.funcs id.id
                  with Not_found -> errorm ~loc:id.loc "Unknown function %s" id.id
                in
                if List.length fn.fn_typ <> n_ids then
                  errorm ~loc "Number of variables does not match number of initializations";
                let res = form_expr fenv e in
                (fn.fn_typ, [res.texpr])
            | _ ->
                if n_ids <> 1 then
                  errorm ~loc "Number of variables does not match number of initializations";
                let res = form_expr fenv e in
                let t = res.texpr.expr_typ in
                if t = Tnil then
                  errorm ~loc "Cannot infer variable type from nil";
                ([t], [res.texpr])
            end
        (* var x1,...,xn = e1,...,en;  (n>=2) *)
        | None, _ when n_inits = n_ids ->
            let rinits = List.map (form_expr fenv) inits in
            let ts =
              List.map (fun r ->
                match r.texpr.expr_typ with
                | Tnil -> errorm ~loc "Cannot infer variable type from nil"
                | t -> t
              ) rinits
            in
            (ts, List.map (fun r -> r.texpr) rinits)
        | _ ->
            errorm ~loc "Invalid form of var declaration"
      in
      let vars =
        List.map2 (fun id t ->
          if id.id <> "_" && Hashtbl.mem fenv.local id.id then
              errorm ~loc:id.loc "Variable %s already defined in this block" id.id;
          let v = new_var id.id id.loc t in
          Hashtbl.add fenv.scope v.v_name v;
          if id.id <> "_" then
            Hashtbl.add fenv.local v.v_name ();
          v
        ) ids var_typs
      in

      let texpr =
        if typed_inits = [] then
          { expr_desc = TEvars vars; expr_typ = Tmany [] }
        else
          let decl = { expr_desc = TEvars vars; expr_typ = Tmany [] } in
          let lhs =
            List.map(fun v ->
              { expr_desc = TEident v; expr_typ = v.v_typ }
            ) vars
          in
          let assign = { expr_desc = TEassign (lhs, typed_inits); expr_typ = Tmany [] } in
          { expr_desc = TEblock [decl; assign]; expr_typ = Tmany [] }
      in
      mk_result texpr
  | PEif (cond_pexpr, then_pexpr, else_pexpr) ->
      let cond_res = form_expr fenv cond_pexpr in
      if not (equal_typ cond_res.texpr.expr_typ Tbool) then
        errorm ~loc "Condition of if must be bool";
      let then_res = form_expr fenv then_pexpr in
      let else_res = form_expr fenv else_pexpr in
      let texpr = {
        expr_desc = TEif (cond_res.texpr, then_res.texpr, else_res.texpr);
        expr_typ = Tmany []
      } in
      let returns = then_res.returns && else_res.returns in
      mk_result ~returns:returns texpr
  | PEreturn pexprs ->
      let exprs =
        List.map (fun pexpr ->
          let res = form_expr fenv pexpr in
          res.texpr
        ) pexprs
      in

      let typs =
        match exprs with
        | [] -> []
        | [expr] ->
            begin match expr.expr_typ with
            | Tmany ts -> ts
            | t        -> [t]
            end
        | _ ->
            List.map (fun expr -> expr.expr_typ) exprs
      in

      let n_typs = List.length typs in
      let n_expected = List.length fenv.rtypes in

      if n_typs <> n_expected then
        errorm ~loc
          "Return has %d value(s) but function expects %d"
          n_typs n_expected;

      List.iter2 (fun typ exp_typ ->
        if not (equal_typ typ exp_typ) then
          errorm ~loc "Return type mismatch"
      ) typs fenv.rtypes;

      let texpr = { expr_desc = TEreturn exprs; expr_typ = Tmany typs } in
      mk_result ~returns:true texpr
  | PEblock pexprs ->
      let benv = {
        fenv with
        scope = Hashtbl.copy fenv.scope;
        local = Hashtbl.create Config.table_sizes.seen_ids;
      } in
      let block_returns = ref false in
      let exprs = List.map (fun pexpr ->
          let res = form_expr benv pexpr in
          if res.returns then block_returns := true;
          res.texpr
      ) pexprs in

      Hashtbl.iter (fun name var ->
        if not (Hashtbl.mem fenv.scope name) then begin
          if name <> "_" && not var.v_used then
            errorm ~loc:var.v_loc "Variable %s declared but not used" name
        end
      ) benv.scope;

      let texpr = { expr_desc = TEblock exprs; expr_typ = Tmany [] } in
      mk_result ~returns:!block_returns texpr
  | PEfor (cond_expr, body_expr) ->
      let cond_res = form_expr fenv cond_expr in
      if not (equal_typ cond_res.texpr.expr_typ Tbool) then
        errorm ~loc "Condition of for must be bool";
      let body_res = form_expr fenv body_expr in
      let texpr = { expr_desc = TEfor (cond_res.texpr, body_res.texpr); expr_typ = Tmany [] } in
      mk_result texpr
  | PEincdec (pexpr, op) ->
      let res = form_expr fenv pexpr in
      let typ = res.texpr.expr_typ in
      if not res.lvalue then
        errorm ~loc "Operand of ++/-- must be assignable";
      if not (equal_typ typ Tint) then
        errorm ~loc "Operand of ++/-- must be int";
      let texpr = { expr_desc = TEincdec (res.texpr, op); expr_typ = Tint } in
      mk_result texpr

let file ~debug:b (imp, dl : Ast.pfile) : Tast.tfile =
  debug := b;

  let genv : env = {
    structs = Hashtbl.create Config.table_sizes.structs;
    funcs   = Hashtbl.create Config.table_sizes.funcs;
  } in

  (* step 1 *)
  List.iter (fun decl ->
    match decl with
    | PDstruct ps ->
        (* check for duplicate struct names *)
        if Hashtbl.mem genv.structs ps.ps_name.id then
          errorm ~loc:ps.ps_name.loc "Duplicate struct name: %s" ps.ps_name.id;

        (* add unformed struct to global env *)
        let s : Tast.structure = {
          s_name   = ps.ps_name.id;
          s_fields = Hashtbl.create Config.table_sizes.seen_ids;
          s_list   = [];
          s_size   = 0
        } in
        Hashtbl.add genv.structs ps.ps_name.id s
    | PDfunction _ -> ()
  ) dl;

  (* step 2a *)
  List.iter (fun decl ->
    match decl with
    | PDstruct _ -> ()
    | PDfunction pf ->
        (* check for duplicate function names *)
        if Hashtbl.mem genv.funcs pf.pf_name.id then
          errorm ~loc:pf.pf_name.loc "Duplicate function name: %s" pf.pf_name.id;

        (* check for duplicate params and well-formed param types *)
        let seen_params = Hashtbl.create Config.table_sizes.seen_ids in
        let fn_params =
          List.map (fun (id, pt) ->
            if Hashtbl.mem seen_params id.id then
              errorm ~loc:id.loc "Duplicate parameter name: %s" id.id;
            Hashtbl.add seen_params id.id ();

            let t = form_type genv.structs pt in
            new_var id.id id.loc t
          ) pf.pf_params;
        in

        (* check for well-formed return types *)
        let fn_typ =
          List.map (
            form_type genv.structs
          ) pf.pf_typ
        in

        (* add function signature to global env *)
        let fn : Tast.function_ = {
          fn_name   = pf.pf_name.id;
          fn_params = fn_params;
          fn_typ    = fn_typ;
        } in
        Hashtbl.add genv.funcs pf.pf_name.id fn
  ) dl;

  (* check for properly formed main function *)
  let main_found = ref false in
    List.iter (fun decl ->
      match decl with
      | PDfunction pf when pf.pf_name.id = "main" ->
          main_found := true;
          if pf.pf_params <> [] then
            errorm ~loc:pf.pf_name.loc "Main function must have no parameters";
          if pf.pf_typ <> [] then
            errorm ~loc:pf.pf_name.loc "Main function must have no return type"
      | _ -> ()
  ) dl;

  if not !main_found then
    errorm "Missing main function";

  (* step 2b *)
  List.iter (fun decl ->
    match decl with
    | PDstruct ps ->
        (* TODO: decide to handle errors or not *)
        let s =
          try Hashtbl.find genv.structs ps.ps_name.id
          with Not_found -> assert false
        in
        let seen_fields = Hashtbl.create Config.table_sizes.seen_ids in

        let rec typ_size typ =
          match typ with
          | Tint | Tbool | Tptr _ | Tstring | Tnil -> 8
          | Tstruct st -> st.s_size
          | _ -> 0
        in

        (* check for duplicate fields and well-formed field types *)
        let size, fields =
          List.fold_left_map (fun ofs (id, pt) ->
            let fname = id.id in
            if Hashtbl.mem seen_fields fname then
              errorm ~loc:id.loc "Duplicate field name %s in struct %s" fname ps.ps_name.id;
            Hashtbl.add seen_fields fname ();

            let typ = form_type genv.structs pt in
            let f : Tast.field = {
              f_name = fname;
              f_typ  = typ;
              f_ofs  = ofs
            } in
            Hashtbl.add s.s_fields fname f;
            (ofs + typ_size typ, f)
          ) 0 ps.ps_fields
        in
        s.s_list <- fields;
        s.s_size <- size
    | PDfunction _ -> ()
  ) dl;

  (* check for recursive structure definition *)
  List.iter (fun decl ->
    match decl with
    | PDstruct ps ->
        let s = Hashtbl.find genv.structs ps.ps_name.id in
        check_rec_struct ps.ps_name.loc s
    | PDfunction _ -> ()
  ) dl;

  (* step 3a *)

  let printed = ref false in

  let tdecls =
    List.map (fun decl ->
      match decl with
      | PDstruct ps ->
          let s = Hashtbl.find genv.structs ps.ps_name.id in
          TDstruct s
      | PDfunction pf ->
          let fn = Hashtbl.find genv.funcs pf.pf_name.id in

          let scope = Hashtbl.create Config.table_sizes.locals in
          let local = Hashtbl.create Config.table_sizes.locals in
          List.iter (fun v ->
            Hashtbl.add scope v.v_name v;
            Hashtbl.add local v.v_name ()
          ) fn.fn_params;

          let fenv = {
            genv    = genv;
            scope   = scope;
            local   = local;
            rtypes  = fn.fn_typ;
            printed = printed;
          } in
          let res = form_expr fenv pf.pf_body in
          let body = res.texpr in

          if fn.fn_typ <> [] && not res.returns then
            errorm ~loc:pf.pf_body.pexpr_loc
              "Function %s does not return a value in all control paths"
              pf.pf_name.id;

          TDfunction (fn, body)
    ) dl
  in

  if !printed && not imp then
    errorm "fmt.Print used but import \"fmt\" not found";
  if imp && not !printed then
    errorm "import \"fmt\" not used";

  tdecls

