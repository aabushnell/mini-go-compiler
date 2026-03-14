open Tast

let rec always_returns (e : expr) : bool =
  match e.expr_desc with
  | TEreturn _ -> true
  | TEblock exprs -> List.exists always_returns exprs
  | TEif (cond, then_e, else_e) -> always_returns then_e && always_returns else_e
  | _ -> false
