open Ast
open Tast
open Oast

module Vmap = Map.Make(struct
  type t = var
  let compare v1 v2 = v1.v_id - v2.v_id
end)

type cell =
  | Const of constant
  | Copy of var

type env = {
  values: cell Vmap.t;
}

let empty_env = { values = Vmap.empty }

let kill env v = { values = Vmap.remove v env.values }

let kill_all env vl = List.fold_left kill env vl

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

let liftTExpr (e: Tast.expr) (d: Oast.expr_desc) : Oast.expr =
  Oast.{ expr_desc = d; expr_typ = e.expr_typ }

let mkOExpr (d: Oast.expr_desc) (ty: typ) : Oast.expr =
  Oast.{ expr_desc = d; expr_typ = ty }

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
  n > 0L && Int64.rem n 2L = 0L &&
  Int64.logand n (Int64.sub n 1L) = 0L

let log2_int64 (n : int64) : int =
  let rec loop k x = if x = 1L then k else loop (k+1) (Int64.div x 2L) in
  loop 0 n

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
  | TEskip       -> liftTExpr e OEskip
  | TEnil        -> liftTExpr e OEnil
  | TEconstant c -> liftTExpr e (OEconstant c)
  | TEnew t      -> liftTExpr e (OEnew t)

  | TEident v ->
      begin match Vmap.find_opt v env.values with
      | Some (Const c) -> liftTExpr e (OEconstant c)
      | Some (Copy u)  -> liftTExpr e (OEident u)
      | None           -> liftTExpr e (OEident v)
      end

  | TEbinop (op, e1, e2) ->
      fold_binop (transl_binop op) (opt_expr env e1) (opt_expr env e2) e.expr_typ

  | TEunop (op, e1) ->
      fold_unop op (opt_expr env e1) e.expr_typ

  | TEcall (f, args) ->
      liftTExpr e (OEcall (f, List.map (opt_expr env) args))
  | TEdot  (e1, f) ->
      liftTExpr e (OEdot (opt_expr env e1, f))
  | TEprint exprs ->
      liftTExpr e (OEprint (List.map (opt_expr env) exprs))
  | TEincdec (e1, op) ->
      liftTExpr e (OEincdec (opt_expr env e1, op))

  | TEassign _ | TEvars _ | TEif _ | TEfor _
  | TEreturn  _ | TEblock _ ->
      fst (opt_stmt env e)

and opt_stmt env (s: Tast.expr) : Oast.expr * env =
  match s.expr_desc with
  | TEskip ->
      (liftTExpr s OEskip, env)
  | TEvars v1 ->
      (liftTExpr s (OEvars v1), kill_all env v1)

  (* reduce direct assignment and add to env if determinable *)
  | TEassign ([{expr_desc = TEident v}], [rv]) ->
      let rv' = opt_expr env rv in
      let lv'  = mkOExpr (OEident v) v.v_typ in
      let env' =
        match rv'.expr_desc with
        | OEconstant c when not v.v_addr ->
            { values = Vmap.add v (Const c) env.values }
        | OEident u when not v.v_addr && not u.v_addr ->
            { values = Vmap.add v (Copy u) env.values }
        | _ ->
            kill env v
      in
      (liftTExpr s (OEassign (lv', rv')), env')
  (* reduce indirect assignment but cannot add to env *)
  | TEassign ([lv], [rv]) ->
      let rv' = opt_expr env rv in
      let lv'  = opt_expr env lv  in
      (liftTExpr s (OEassign (lv', rv')), env)
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
          (liftTExpr s (OEif (cond', then_', else_')), merge_env env1 env2)
      end

  (* check if loops are ever taken *)
  | TEfor (cond, body) ->
      (* we cannot know when loop body variables were assigned *)
      let loop_env = kill_all env (assigned_vars body) in
      let cond' = opt_expr loop_env cond in
      begin match cond'.expr_desc with
      | OEconstant (Cbool false) ->
          (* loop never taken *)
          (liftTExpr s OEskip, env)
      | _ ->
          let (body', _) = opt_stmt loop_env body in
          (liftTExpr s (OEfor (cond', body')), loop_env)
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
        | []  -> liftTExpr s OEskip
        | [x] -> x
        | _   -> liftTExpr s (OEblock stmts'')
      in
      (result, env')

  | TEreturn []  -> (liftTExpr s (OEreturn None), env)
  | TEreturn [e] -> (liftTExpr s (OEreturn (Some (opt_expr env e))), env)
  | TEreturn _   -> assert false

  | TEprint exprs ->
      (liftTExpr s (OEprint (List.map (opt_expr env) exprs)), env)

  | TEincdec (e1, op) ->
      let env' = match e1.expr_desc with
        | TEident v -> kill env v
        | _ -> env
      in
      (liftTExpr s (OEincdec (opt_expr env e1, op)), env')
  | _ ->
      (opt_expr env s, env)

and opt_block env : Tast.expr list -> Oast.expr list * env = function
  | [] -> ([], env)
  | s :: tl ->
      let (s', env')   = opt_stmt env s in
      let (tl', env'') = opt_block env' tl in
      (s' :: tl', env'')

and assigned_vars (e: Tast.expr) : var list =
  match e.expr_desc with
  | TEassign ([{expr_desc = TEident v}], _) -> [v]
  | TEincdec ({expr_desc = TEident v}, _)   -> [v]
  | TEblock stmts  -> List.concat_map assigned_vars stmts
  | TEif (_, a, b) -> assigned_vars a @ assigned_vars b
  | TEfor (_, b)   -> assigned_vars b
  | TEvars vl      -> vl
  | _              -> []

let function_ f (body: Tast.expr) : Oast.odecl =
  let (body', _) = opt_stmt empty_env body in
  ODfunction (f, body')

let decl : Tast.tdecl -> Oast.odecl = function
  | TDfunction (f, body) -> function_ f body
  | TDstruct s           -> ODstruct s

let file ?debug:(_=false) (dl: Tast.tfile) : Oast.ofile =
  List.map decl dl
