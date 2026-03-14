open Tast

(* traverses entire tree and collects declared variables *)
let rec collect_declared_vars (e : expr) : var list =
  match e.expr_desc with
  | TEvars vars -> vars
  | TEif (_, then_e, else_e) ->
      collect_declared_vars then_e @ collect_declared_vars else_e
  | TEblock exprs -> List.flatten (List.map collect_declared_vars exprs)
  | TEfor (_, body) -> collect_declared_vars body
  | _ -> []
