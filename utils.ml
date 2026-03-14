open Ast
open Tast

let rec string_of_ptyp (t : ptyp) : string =
  match t with
  | PTident ident -> ident.id
  | PTptr ptr -> "*" ^ string_of_ptyp ptr

let rec string_of_typ = function
  | Tint -> "int"
  | Tbool -> "bool"
  | Tstring -> "string"
  | Tnil -> "nil"
  | Tstruct s -> s.s_name
  | Tptr t -> "*" ^ string_of_typ t
  | Tmany ts -> "(" ^ String.concat ", " (List.map string_of_typ ts) ^ ")"

let string_of_binop = function
  | Badd -> "+"
  | Bsub -> "-"
  | Bmul -> "*"
  | Bdiv -> "/"
  | Bmod -> "%"
  | Beq -> "=="
  | Bne -> "!="
  | Blt -> "<"
  | Ble -> "<="
  | Bgt -> ">"
  | Bge -> ">="
  | Band -> "&&"
  | Bor -> "||"

let check_duplicates ~get_key ~on_duplicate list =
  begin
    let seen = Hashtbl.create 10 in

    List.iter
      (fun elem ->
        begin
          let key = get_key elem in
          match Hashtbl.find_opt seen key with
          | Some first_occurence -> on_duplicate first_occurence elem
          | None -> Hashtbl.add seen key elem
        end)
      list
  end

let rec types_equal (t1 : typ) (t2 : typ) : bool =
  match (t1, t2) with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tnil, Tnil -> true
  | Tptr t1', Tptr t2' -> types_equal t1' t2'
  | Tstruct s1, Tstruct s2 -> s1.s_name = s2.s_name
  | Tnil, Tptr _ | Tptr _, Tnil -> true (* nil compatible with any pointer *)
  | _ -> false
