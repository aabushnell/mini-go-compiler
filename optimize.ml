open Ast
open Tast
open Oast

let enable_copy_propagation = false

module Vmap = Map.Make (struct
  type t = var
  let compare v1 v2 = Int.compare v1.v_id v2.v_id
end)

type item =
  | Const of constant
  | Copy of var

type env = {
  values: item Vmap.t;
}

let empty_env = { values = Vmap.empty }

let kill env var = { values = Vmap.remove var env.values }

let kill_all env vars = List.fold_left kill env vars

let rec addr_targets (expr: Tast.expr) : var list =
  match expr.expr_desc with
  | TEunop (Uamp, {expr_desc = TEident var}) -> [var]
  | TEunop (_, expr1)          -> addr_targets expr1
  | TEbinop (_, expr1, expr2)  -> addr_targets expr1 @ addr_targets expr2
  | TEcall (_, args)           -> List.concat_map addr_targets args
  | _                          -> []

let kill_addr_targets env expr = kill_all env (addr_targets expr)

let merge_env env1 env2 =
  { values = Vmap.merge (fun _ a b ->
      match a, b with
      | Some (Const (Cint x)), Some (Const (Cint y)) when x = y ->
          Some (Const (Cint x))
      | Some (Const(Cbool x)), Some (Const (Cbool y)) when x = y ->
          Some (Const (Cbool x))
      | Some (Copy x), Some (Copy y) when x.v_id = y.v_id ->
          Some (Copy x)
      | _ -> None
    ) env1.values env2.values 
  }

let lowerTExpr (expr: Tast.expr) (desc: Oast.expr_desc) : Oast.expr =
  { expr_desc = desc; expr_typ = expr.expr_typ }

let mkOExpr (desc: Oast.expr_desc) (typ: typ) : Oast.expr =
  { expr_desc = desc; expr_typ = typ }

let transl_binop : Ast.binop -> Oast.binop = function
  | Badd -> Oast.Badd
  | Bsub -> Oast.Bsub
  | Bmul -> Oast.Bmul
  | Bdiv -> Oast.Bdiv
  | Bmod -> Oast.Bmod
  | Beq  -> Oast.Beq
  | Bne  -> Oast.Bne
  | Blt  -> Oast.Blt
  | Ble  -> Oast.Ble
  | Bgt  -> Oast.Bgt
  | Bge  -> Oast.Bge
  | Band -> Oast.Band
  | Bor  -> Oast.Bor

let is_power_of_two (n : int64) : bool =
  let is_pos = n > 0L in
  let single_bit_set = Int64.logand n (Int64.sub n 1L) = 0L in
  is_pos && single_bit_set

let log2_int64 (n : int64) : int =
  let rec count_pow2 k rem =
    if rem = 1L then
      k
    else
      count_pow2 (k + 1) (Int64.div rem 2L) in
  count_pow2 0 n

let fold_binop op e1 e2 typ : expr =
  let mk d = mkOExpr d typ in
  let c1 = match e1.expr_desc with
           | OEconstant c -> Some c
           | _ -> None in
  let c2 = match e2.expr_desc with
           | OEconstant c -> Some c
           | _ -> None in
  match op, c1, c2 with
  (* constant evaluation reductions *)
  | Oast.Badd, Some (Cint a), Some (Cint b) ->
      mk (OEconstant (Cint (Int64.add a b)))
  | Oast.Bsub, Some (Cint a), Some (Cint b) ->
      mk (OEconstant (Cint (Int64.sub a b)))
  | Oast.Bmul, Some (Cint a), Some (Cint b) ->
      mk (OEconstant (Cint (Int64.mul a b)))
  | Oast.Bdiv, Some (Cint a), Some (Cint b) when b <> 0L ->
      mk (OEconstant (Cint (Int64.div a b)))
  | Oast.Bmod, Some (Cint a), Some (Cint b) when b <> 0L ->
      mk (OEconstant (Cint (Int64.rem a b)))
  | Oast.Beq, Some (Cint a), Some (Cint b) ->
      mk (OEconstant (Cbool (a = b)))
  | Oast.Bne, Some (Cint a), Some (Cint b) ->
      mk (OEconstant (Cbool (a <> b)))
  | Oast.Blt, Some (Cint a), Some (Cint b) ->
      mk (OEconstant (Cbool (a < b)))
  | Oast.Ble, Some (Cint a), Some (Cint b) ->
      mk (OEconstant (Cbool (a <= b)))
  | Oast.Bgt, Some (Cint a), Some (Cint b) ->
      mk (OEconstant (Cbool (a > b)))
  | Oast.Bge, Some (Cint a), Some (Cint b) ->
      mk (OEconstant (Cbool (a >= b)))
  | Oast.Band, Some (Cbool a), Some (Cbool b) ->
      mk (OEconstant (Cbool (a && b)))
  | Oast.Bor, Some (Cbool a), Some (Cbool b) ->
      mk (OEconstant (Cbool (a || b)))

  (* algebraic reductions *)
  | Oast.Badd, Some (Cint 0L), _ -> e2
  | Oast.Badd, _, Some (Cint 0L) -> e1
  | Oast.Bsub, _, Some (Cint 0L) -> e1
  | Oast.Bmul, Some (Cint 0L), _ ->
      mk (OEconstant (Cint 0L))
  | Oast.Bmul, _, Some (Cint 0L) ->
      mk (OEconstant (Cint 0L))
  | Oast.Bmul, Some (Cint 1L), _ -> e2
  | Oast.Bmul, _, Some (Cint 1L) -> e1
  | Oast.Bdiv, _, Some (Cint 1L) -> e1
  | Oast.Band, Some (Cbool false), _ | Band, _, Some (Cbool false) ->
      mk (OEconstant (Cbool false))
  | Oast.Bor, Some (Cbool true), _ | Bor, _, Some (Cbool true) ->
      mk (OEconstant (Cbool true))
  | Oast.Band, Some (Cbool true), _ -> e2
  | Oast.Bor, Some (Cbool false), _ -> e2

  (* alternate instruction reductions *)
  | Oast.Bmul, _, Some (Cint n) when is_power_of_two n ->
      let k = { expr_desc = OEconstant (Cint (Int64.of_int (log2_int64 n)));
                expr_typ = Tint } in
      mk (OEbinop (Bshl, e1, k))
  | Oast.Bdiv, _, Some (Cint n) when is_power_of_two n ->
      let k = { expr_desc = OEconstant (Cint (Int64.of_int (log2_int64 n)));
                expr_typ = Tint } in
      mk (OEbinop (Bshr, e1, k))

  | _ -> mk (OEbinop (op, e1, e2))

let fold_unop op e typ : expr =
  let mk d = mkOExpr d typ in
  match op, e.expr_desc with
  (* constant evaluation *)
  | Uneg, OEconstant (Cint n) ->
      mk (OEconstant (Cint (Int64.neg n)))
  | Unot, OEconstant (Cbool b) ->
      mk (OEconstant (Cbool (not b)))
  (* double negation *)
  | Unot, OEunop (Unot, e')    -> e'
  | _ -> mk (OEunop (op, e))

let rec opt_expr env (e: Tast.expr) : Oast.expr =
  match e.expr_desc with
  | TEskip       -> lowerTExpr e OEskip
  | TEnil        -> lowerTExpr e OEnil
  | TEconstant c -> lowerTExpr e (OEconstant c)
  | TEnew t      -> lowerTExpr e (OEnew t)

  | TEident v ->
      begin match Vmap.find_opt v env.values with
      | Some (Const c) -> lowerTExpr e (OEconstant c)
      | Some (Copy u)  -> lowerTExpr e (OEident u)
      | None           -> lowerTExpr e (OEident v)
      end

  | TEbinop (op, e1, e2) ->
      fold_binop (transl_binop op) (opt_expr env e1) (opt_expr env e2) e.expr_typ

  | TEunop (Uamp, e1) ->
      lowerTExpr e (OEunop (Uamp, opt_laddr env e1))
  | TEunop (op, e1) ->
      fold_unop op (opt_expr env e1) e.expr_typ

  | TEcall (f, args) ->
      lowerTExpr e (OEcall (f, List.map (opt_expr env) args))
  | TEdot  (e1, f) ->
      lowerTExpr e (OEdot (opt_expr env e1, f))
  | TEprint exprs ->
      lowerTExpr e (OEprint (List.map (opt_expr env) exprs))
  | TEincdec (e1, op) ->
      lowerTExpr e (OEincdec (opt_expr env e1, op))

  | TEassign _ | TEvars _ | TEif _ | TEfor _
  | TEreturn  _ | TEblock _ ->
      fst (opt_stmt env e)

and opt_laddr env (e: Tast.expr) : Oast.expr =
  match e.expr_desc with
  | TEident v ->
      mkOExpr (OEident v) e.expr_typ
  | TEdot (e1, f) ->
      mkOExpr (OEdot (opt_laddr env e1, f)) e.expr_typ
  | TEunop (Ustar, e1) ->
      mkOExpr (OEunop (Ustar, opt_expr env e1)) e.expr_typ
  | _ ->
      opt_expr env e

and opt_stmt env (s: Tast.expr) : Oast.expr * env =
  match s.expr_desc with
  | TEskip ->
      (lowerTExpr s OEskip, env)
  | TEvars v1 ->
      (lowerTExpr s (OEvars v1), kill_all env v1)

  (* reduce direct assignment and add to env if determinable *)
  | TEassign ([{expr_desc = TEident v}], [rv]) ->
      let rv' = opt_expr env rv in
      let lv'  = mkOExpr (OEident v) v.v_typ in
      let env' = kill_addr_targets env rv in
      let env'' =
        match rv'.expr_desc with
        | OEconstant c when not v.v_addr ->
            { values = Vmap.add v (Const c) env.values }
        | OEident u when not v.v_addr && not u.v_addr && enable_copy_propagation ->
            (* experimental! does not produce correct behavior for 'a, b = b, a' *)
            { values = Vmap.add v (Copy u) env.values }
        | _ ->
            kill env' v
      in
      (lowerTExpr s (OEassign (lv', rv')), env'')
  (* reduce indirect assignment but cannot add to env *)
  | TEassign ([lv], [rv]) ->
      let rv' = opt_expr env rv in
      let lv'  = opt_expr env lv  in
      (lowerTExpr s (OEassign (lv', rv')), env)
  | TEassign _ -> assert false

  (* if constant cond then remove branch *)
  | TEif (cond, then_, else_) ->
      let cond' = opt_expr env cond in
      begin match cond'.expr_desc with
      | OEconstant (Cbool true)  -> opt_stmt env then_
      | OEconstant (Cbool false) -> opt_stmt env else_
      | _ ->
          let (then_', env1) = opt_stmt env then_ in
          let (else_', env2) = opt_stmt env else_ in
          (lowerTExpr s (OEif (cond', then_', else_')), merge_env env1 env2)
      end

  (* check if loops are ever taken *)
  | TEfor (cond, body) ->
      (* we cannot know when loop body variables were assigned *)
      let loop_env = kill_all env (assigned_vars body) in
      let cond' = opt_expr loop_env cond in
      begin match cond'.expr_desc with
      | OEconstant (Cbool false) ->
          (* loop never taken *)
          (lowerTExpr s OEskip, env)
      | _ ->
          let (body', _) = opt_stmt loop_env body in
          (lowerTExpr s (OEfor (cond', body')), loop_env)
      end

  (* optimize blocks and filter out skips left behind *)
  | TEblock stmts ->
      let (stmts', env') = opt_block env stmts in
      let stmts'' =
        List.filter (fun x ->
          match x.expr_desc with
          | OEskip -> false
          | _ -> true
        ) stmts' in
      let result = match stmts'' with
        | []  -> lowerTExpr s OEskip
        | [x] -> x
        | _   -> lowerTExpr s (OEblock stmts'')
      in
      (result, env')

  | TEreturn []  -> (lowerTExpr s (OEreturn None), env)
  | TEreturn [e] -> (lowerTExpr s (OEreturn (Some (opt_expr env e))), env)
  | TEreturn _   -> assert false

  | TEprint exprs ->
      (lowerTExpr s (OEprint (List.map (opt_expr env) exprs)), env)

  (* check for updated variable *)
  | TEincdec (e1, op) ->
      let env' = match e1.expr_desc with
        | TEident v -> kill env v
        | _ -> env
      in
      (lowerTExpr s (OEincdec (opt_expr env e1, op)), env')

  | TEcall (f, args) ->
      let opt_args = List.map (opt_expr env) args in
      let env' = kill_all env (List.concat_map addr_targets args) in
      (lowerTExpr s (OEcall (f, opt_args)), env')
  | _ ->
      (opt_expr env s, env)

and opt_block env (stmts: Tast.expr list) : Oast.expr list * env =
  match stmts with
  | [] -> ([], env)
  | stmt :: rest ->
      let (stmt', env') = opt_stmt env stmt in
      let (rest', env_final) = opt_block env' rest in
      (stmt' :: rest', env_final)

and assigned_vars (e: Tast.expr) : var list =
  match e.expr_desc with
  | TEassign ([{expr_desc = TEident v}], _) -> [v]
  | TEincdec ({expr_desc = TEident v}, _)   -> [v]
  | TEblock stmts    -> List.concat_map assigned_vars stmts
  | TEif (_, a, b)   -> assigned_vars a @ assigned_vars b
  | TEfor (_, b)     -> assigned_vars b
  | TEvars vl        -> vl
  | TEcall (_, args) ->
      List.concat_map (fun (arg: Tast.expr) ->
        match arg.expr_desc with
        | TEunop (Uamp, {expr_desc = TEident v}) -> [v]
        | _ -> []
      ) args
  | _              -> []

let function_ f (body: Tast.expr) : Oast.odecl =
  let (body', _) = opt_stmt empty_env body in
  ODfunction (f, body')

let decl : Tast.tdecl -> Oast.odecl = function
  | TDfunction (f, body) -> function_ f body
  | TDstruct s           -> ODstruct s

let file ?debug:(_=false) (dl: Tast.tfile) : Oast.ofile =
  List.map decl dl
