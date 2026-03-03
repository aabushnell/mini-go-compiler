
(** Code generation for Mini Go programs (TODO) *)

open Format
open Ast
open Tast
open X86_64

let debug = ref false

let iter f = List.fold_left (fun code x -> code ++ f x) nop
let iter2 f = List.fold_left2 (fun code x y -> code ++ f x y) nop

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

(* NOTE: data generation *)

let string_literals = ref ([] : (string * label) list)

let get_string_label s =
  try List.assoc s !string_literals
  with Not_found ->
    let lbl = new_label () in
    string_literals := (s, lbl) :: !string_literals;
    lbl

let generate_data () =
  List.fold_left (fun code (s, lbl) ->
    code ++ label lbl ++ string s
  ) nop (List.rev !string_literals)

(* NOTE: frame management *)

type frame = {
  mutable stack_offset: int;  (* next local offset, negative from %rbp *)
  locals: (int, int) Hashtbl.t;  (* v_id -> offset from %rbp *)
  params: (int, int) Hashtbl.t; (* v_id -> offset from %rbp (positive) *)
}

let new_frame () = {
  stack_offset = -8;
  locals = Hashtbl.create 16;
  params = Hashtbl.create 16;
}

(* NOTE: expression generation *)

let rec gen_expr frame e = match e.expr_desc with
  | TEconstant c ->
      begin match c with
      | Cbool b ->
          movq (imm (if b then 1 else 0)) (reg rax)
      | Cint i ->
          movq (imm64 i) (reg rax)
      | Cstring s ->
          let lbl = get_string_label s in
          leaq (lab lbl) rax
      end
  | TEbinop (op, expr1, expr2) ->
      gen_expr frame expr1 ++
      pushq (reg rax) ++
      gen_expr frame expr2 ++
      movq (reg rax) (reg rcx) ++
      popq rax ++
      (
        match op with
        | Badd -> addq (reg rcx) (reg rax)
        | Bsub -> subq (reg rcx) (reg rax)
        | Bmul -> imulq (reg rcx) (reg rax)
        | Bdiv -> cqto ++ idivq (reg rcx)
        | _ ->
            failwith "Bop Not Implemented";
      )
  | TEident var ->
      let offset =
        try Hashtbl.find frame.locals var.v_id
        with Not_found ->
          try Hashtbl.find frame.params var.v_id
          with Not_found -> failwith ("Unknown variable: " ^ var.v_name)
      in
      movq (ind ~ofs:offset rbp) (reg rax)
  | TEassign (lhs_exprs, rhs_exprs) ->
      gen_expr frame (List.hd rhs_exprs) ++
      pushq (reg rax) ++
      (
        match (List.hd lhs_exprs).expr_desc with
        | TEident var ->
            popq rax ++
            let offset =
              try Hashtbl.find frame.locals var.v_id
              with Not_found -> 
                try Hashtbl.find frame.params var.v_id
                with Not_found -> failwith ("Unknown variable: " ^ var.v_name)
            in
            movq (reg rax) (ind ~ofs:offset rbp)
        | _ ->
            failwith "Complex lvalues Not Implemented";
      )
  | TEprint exprs ->
      gen_print frame exprs
  | _ ->
      nop (* TODO: continue implementation *)

and gen_print frame exprs =
  List.fold_left (fun code expr ->
    (* Evaluate expression to %rax *)
    code ++
    gen_expr frame expr ++
    (* move to %rsi (2nd arg) *)
    movq (reg rax) (reg rsi) ++
    (* Get format string - for now assume int *)
    let fmt_lbl = get_string_label "%d\n" in
    leaq (lab fmt_lbl) rdi ++
    (* clear %rax for variadic function *)
    xorq (reg rax) (reg rax) ++
    call "printf_" ++
    addq (imm 16) (reg rsp)      (* clean up stack *)
  ) nop exprs

(* NOTE: statement generation *)

let rec gen_stmt frame s = match s.expr_desc with
  | TEvars vars ->
      List.fold_left (fun code v ->
        let offset = frame.stack_offset in
        Hashtbl.add frame.locals v.v_id offset;
        frame.stack_offset <- offset - 8;
        code
      ) nop vars
  | TEif (cond, then_, else_) ->
      failwith "If Not Implemented";
  | TEreturn exprs ->
      failwith "Return Not Implemented";
  | TEblock exprs ->
      List.fold_left (fun code s ->
        code ++ gen_stmt frame s
      ) nop exprs
  | TEfor (cond, body) ->
      failwith "For Not Implemented";
  | _ ->
      gen_expr frame s

(* NOTE: function generation *)

let function_ asm_name (f, body) =
  (* Build frame with parameters *)
  let frame = new_frame () in
  (* Parameters start at 16(%rbp): return addr + saved %rbp *)
  let param_offset = ref 16 in
  List.iter (fun v ->
    Hashtbl.add frame.params v.v_id !param_offset;
    param_offset := !param_offset + 8
  ) f.fn_params;

  (* Generate function code *)
  label asm_name ++
  pushq (reg rbp) ++
  movq (reg rsp) (reg rbp) ++
  (* Body *)
  gen_stmt frame body ++
  (* Return default 0 if no explicit return *)
  xorq (reg rax) (reg rax) ++
  movq (reg rbp) (reg rsp) ++
  popq rbp ++
  ret

let find_main (dl: tfile) =
  List.find_opt (function
    | TDfunction (f, _) -> f.fn_name = "main"
    | _ -> false
  ) dl

let file ?debug:(b=false) (dl: Tast.tfile): X86_64.program =
  debug := b;
  string_literals := [];

  let text_code = 
    List.fold_left (fun code d -> match d with
      | TDfunction (f, e) ->
          let asm_name = if f.fn_name = "main" then "main_go" else f.fn_name in
          code ++ function_ asm_name (f, e)
      | TDstruct _ -> code  (* nothing to generate for structs *)
    ) nop dl
  in

  let go_main = match find_main dl with
    | Some (TDfunction (f, _)) -> 
        if f.fn_name = "main" then "main_go" else f.fn_name
    | _ -> "main_missing"
  in

  { text =
      globl "main" ++ label "main" ++
      call go_main ++
      movq (reg rax) (reg rdi) ++
      call "exit" ++
      ret ++
      text_code ++
      inline "
      # TODO some auxiliary assembly functions, if needed
      "
  ++ aligned_call_wrapper ~f:"malloc" ~newf:"malloc_"
  ++ aligned_call_wrapper ~f:"calloc" ~newf:"calloc_"
  ++ aligned_call_wrapper ~f:"printf" ~newf:"printf_"
;
    data =
      generate_data ()
    ;
  }
