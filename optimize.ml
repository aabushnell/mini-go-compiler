open Ast
open Tast

module Vmap = Map.Make(struct
  type t = var
  let compare v1 v2 = v1.v_id - v2.v_id
end)

type env = {
  consts: constant Vmap.t;
}

let empty_env = { consts = Vmap.empty }

let kill env v = { consts = Vmap.remove v env.consts }

let kill_all env vl = List.fold_left kill env vl

let merge_env env1 env2 =
  { consts = Vmap.merge (fun _ a b ->
      match a, b with
      | Some (Cint x), Some (Cint y) when x = y -> Some (Cint x)
      | Some (Cbool x), Some (Cbool y) when x = y -> Some (Cbool x)
      | _ -> None
    ) env1.consts env2.consts }

let is_power_of_two (n : int64) : bool =
  n > 0L && Int64.rem n 2L = 0L &&
  Int64.logand n (Int64.sub n 1L) = 0L

let log2_int64 (n : int64) : int =
  let rec loop k x = if x = 1L then k else loop (k+1) (Int64.div x 2L) in
  loop 0 n

let fold_binop op e1 e2 typ : expr =
  let make d = { expr_desc = d; expr_typ = typ } in
  let c1 = match e1.expr_desc with
           | TEconstant c -> Some c
           | _ -> None in
  let c2 = match e2.expr_desc with
           | TEconstant c -> Some c
           | _ -> None in
  match op, c1, c2 with
  (* constant evaluation reductions *)
  | Badd, Some (Cint a), Some (Cint b) ->
      make (TEconstant (Cint (Int64.add a b)))
  | Bsub, Some (Cint a), Some (Cint b) ->
      make (TEconstant (Cint (Int64.sub a b)))
  | Bmul, Some (Cint a), Some (Cint b) ->
      make (TEconstant (Cint (Int64.mul a b)))
  | Bdiv, Some (Cint a), Some (Cint b) when b <> 0L ->
      make (TEconstant (Cint (Int64.div a b)))
  | Bmod, Some (Cint a), Some (Cint b) when b <> 0L ->
      make (TEconstant (Cint (Int64.rem a b)))
  | Beq, Some (Cint a), Some (Cint b) ->
      make (TEconstant (Cbool (a = b)))
  | Bne, Some (Cint a), Some (Cint b) ->
      make (TEconstant (Cbool (a <> b)))
  | Blt, Some (Cint a), Some (Cint b) ->
      make (TEconstant (Cbool (a < b)))
  | Ble, Some (Cint a), Some (Cint b) ->
      make (TEconstant (Cbool (a <= b)))
  | Bgt, Some (Cint a), Some (Cint b) ->
      make (TEconstant (Cbool (a > b)))
  | Bge, Some (Cint a), Some (Cint b) ->
      make (TEconstant (Cbool (a >= b)))
  | Band, Some (Cbool a), Some (Cbool b) ->
      make (TEconstant (Cbool (a && b)))
  | Bor, Some (Cbool a), Some (Cbool b) ->
      make (TEconstant (Cbool (a || b)))

  (* algebraic reductions *)
  | Badd, Some (Cint 0L), _ -> e2
  | Badd, _, Some (Cint 0L) -> e1
  | Bsub, _, Some (Cint 0L) -> e1
  | Bmul, Some (Cint 0L), _ ->
      make (TEconstant (Cint 0L))
  | Bmul, _, Some (Cint 0L) ->
      make (TEconstant (Cint 0L))
  | Bmul, Some (Cint 1L), _ -> e2
  | Bmul, _, Some (Cint 1L) -> e1
  | Bdiv, _, Some (Cint 1L) -> e1
  | Band, Some (Cbool false), _ | Band, _, Some (Cbool false) ->
      make (TEconstant (Cbool false))
  | Bor, Some (Cbool true), _ | Bor, _, Some (Cbool true) ->
      make (TEconstant (Cbool true))
  | Band, Some (Cbool true), _ -> e2
  | Bor, Some (Cbool false), _ -> e2

  (* alternate instruction reductions *)
  (*TODO: decide how/where to handle shifts *)
  | Bmul, _, Some (Cint n) when is_power_of_two n ->
      let k = { expr_desc = TEconstant (Cint (Int64.of_int (log2_int64 n)));
                expr_typ = Tint } in
      make (TEbinop (Bshl, e1, k))
  | Bdiv, _, Some (Cint n) when is_power_of_two n ->
      let k = { expr_desc = TEconstant (Cint (Int64.of_int (log2_int64 n)));
                expr_typ = Tint } in
      make (TEbinop (Bshr, e1, k))

  | _ -> make (TEbinop (op, e1, e2))

let fold_unop op e typ : expr =
  let make d = { expr_desc = d; expr_typ = typ } in
  match op, e.expr_desc with
  (* constant evaluation *)
  | Uneg, TEconstant (Cint n)  -> make (TEconstant (Cint (Int64.neg n)))
  | Unot, TEconstant (Cbool b) -> make (TEconstant (Cbool (not b)))
  (* double negation *)
  | Unot, TEunop (Unot, e')    -> e'
  | _ -> make (TEunop (op, e))

let rec opt_expr env e =
  let mk d = { e with expr_desc = d } in
  match e.expr_desc with
  | TEskip | TEnil | TEconstant _ | TEnew _ -> e

  | TEident v ->
      begin match Vmap.find_opt v env.consts with
      | Some c -> mk (TEconstant c)
      | None   -> e
      end

  | TEbinop (op, e1, e2) ->
      fold_binop op (opt_expr env e1) (opt_expr env e2) e.expr_typ

  | TEunop (op, e1) ->
      fold_unop op (opt_expr env e1) e.expr_typ

  | TEcall (f, args)  -> mk (TEcall (f, List.map (opt_expr env) args))
  | TEdot  (e1, f)    -> mk (TEdot (opt_expr env e1, f))
  | TEprint exprs     -> mk (TEprint (List.map (opt_expr env) exprs))
  | TEincdec (e1, op) -> mk (TEincdec (opt_expr env e1, op))
  | TEassign _ | TEvars _ | TEif _ | TEfor _
  | TEreturn  _ | TEblock _ ->
      fst (opt_stmt env e)

and opt_stmt env s =
  let mk d = { s with expr_desc = d } in
  match s.expr_desc with
  | TEskip -> (s, env)
  | TEvars v1 -> (s, kill_all env v1)
  | TEassign ([{expr_desc = TEident v} as lv], [rhs]) ->
      let rhs' = opt_expr env rhs in
      let env' =
        match rhs'.expr_desc with
        | TEconstant c ->
            if not v.v_addr then { consts = Vmap.add v c env.consts }
            else kill env v
        | _ -> kill env v
      in
      (mk (TEassign ([lv], [rhs'])), env')
  | TEassign ([lv], [rhs]) ->
      let rhs' = opt_expr env rhs in
      let lv'  = opt_expr env lv  in
      (mk (TEassign ([lv'], [rhs'])), env)
  | TEassign _ -> assert false
  | TEif (cond, then_, else_) ->
      let cond' = opt_expr env cond in
      begin match cond'.expr_desc with
      | TEconstant (Cbool true)  -> opt_stmt env then_
      | TEconstant (Cbool false) -> opt_stmt env else_
      | _ ->
          let (then_', env1) = opt_stmt env then_ in
          let (else_', env2) = opt_stmt env else_ in
          (mk (TEif (cond', then_', else_')), merge_env env1 env2)
      end
  | TEfor (cond, body) ->
      let loop_env = kill_all env (assigned_vars body) in
      let cond' = opt_expr loop_env cond in
      begin match cond'.expr_desc with
      | TEconstant (Cbool false) ->
          (* Dead loop: body never executes, whole thing is a no-op *)
          ({ s with expr_desc = TEskip }, env)
      | _ ->
          let (body', _) = opt_stmt loop_env body in
          (mk (TEfor (cond', body')), loop_env)
      end
  | TEblock stmts ->
      let (stmts', env') = opt_block env stmts in
      let stmts'' = List.filter (fun s -> s.expr_desc <> TEskip) stmts' in
      let result = match stmts'' with
        | []  -> { s with expr_desc = TEskip }
        | [x] -> x
        | _   -> mk (TEblock stmts'')
      in
      (result, env')
  | TEreturn []  -> (s, env)
  | TEreturn [e] -> (mk (TEreturn [opt_expr env e]), env)
  | TEreturn _   -> assert false
  | TEprint exprs -> (mk (TEprint (List.map (opt_expr env) exprs)), env)
  | TEincdec (e1, op) ->
      let env' = match e1.expr_desc with
        | TEident v -> kill env v
        | _ -> env
      in
      (mk (TEincdec (opt_expr env e1, op)), env')
  | _ -> (opt_expr env s, env)

and opt_block env = function
  | []      -> ([], env)
  | s :: tl ->
      let (s', env')   = opt_stmt  env  s  in
      let (tl', env'') = opt_block env' tl in
      (s' :: tl', env'')

and assigned_vars e : var list =
  match e.expr_desc with
  | TEassign ([{expr_desc = TEident v}], _) -> [v]
  | TEincdec ({expr_desc = TEident v}, _)   -> [v]
  | TEblock stmts  -> List.concat_map assigned_vars stmts
  | TEif (_, a, b) -> assigned_vars a @ assigned_vars b
  | TEfor (_, b)   -> assigned_vars b
  | TEvars vl      -> vl
  | _              -> []

let function_ f body =
  let (body', _) = opt_stmt empty_env body in
  TDfunction (f, body')

let decl = function
  | TDfunction (f, body) -> function_ f body
  | TDstruct _ as d      -> d

let file ?debug:(_=false) dl =
  List.map decl dl
