
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

let get_empty_string_label =
  let lbl = get_string_label "" in
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

let rec typ_size = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | Tstruct s -> s.s_size
  | _ -> failwith "Unsupported type for size"

let rec gen_expr frame e = match e.expr_desc with
  | TEskip -> nop
  | TEconstant c ->
      begin match c with
      | Cbool b ->
          movq (imm (if b then 1 else 0)) (reg rax)
      | Cint i ->
          movabsq (imm64 i) rax
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
        | Bmod -> cqto ++ idivq (reg rcx) ++ movq (reg rdx) (reg rax)

        | Beq -> cmpq (reg rcx) (reg rax) ++ sete (reg al) ++ movzbq (reg al) (rax)
        | Bne -> cmpq (reg rcx) (reg rax) ++ setne (reg al) ++ movzbq (reg al) (rax)
        | Blt -> cmpq (reg rcx) (reg rax) ++ setl (reg al) ++ movzbq (reg al) (rax)
        | Ble -> cmpq (reg rcx) (reg rax) ++ setle (reg al) ++ movzbq (reg al) (rax)
        | Bgt -> cmpq (reg rcx) (reg rax) ++ setg (reg al) ++ movzbq (reg al) (rax)
        | Bge -> cmpq (reg rcx) (reg rax) ++ setge (reg al) ++ movzbq (reg al) (rax)

        | Band -> andq (reg rcx) (reg rax)
        | Bor  -> orq (reg rcx) (reg rax)

        | Bshl -> shlq (reg rcx) (reg rax)
        | Bshr -> shrq (reg rcx) (reg rax)
      )
  | TEunop (op, expr) ->
      begin match op with
      | Uneg ->
          gen_expr frame expr ++
          negq (reg rax)
      | Unot ->
          gen_expr frame expr ++
          testq (reg rax) (reg rax) ++
          setz (reg al) ++
          movzbq (reg al) rax
      | Uamp ->
          gen_laddr frame expr
      | Ustar ->
          gen_expr frame expr ++
          begin match expr.expr_typ with
          | Tptr (Tstruct _) ->
              nop
          | _ ->
              movq (ind rax) (reg rax)
          end
      end
  | TEnil -> movq (imm 0) (reg rax)
  | TEnew typ ->
      let size = typ_size typ in
      movq (imm 1) (reg rdi) ++
      movq (imm size) (reg rsi) ++
      call "calloc_"
  | TEcall (fn, args) ->
      let push_args =
        List.fold_left (fun code arg ->
          code ++
          gen_expr frame arg ++
          pushq (reg rax)
        ) nop (List.rev args)
      in
      push_args ++
      call fn.fn_name ++
      addq (imm (8 * List.length args)) (reg rsp)
  | TEident var ->
      let offset =
        try Hashtbl.find frame.locals var.v_id
        with Not_found ->
          try Hashtbl.find frame.params var.v_id
          with Not_found -> failwith ("Unknown variable: " ^ var.v_name)
      in
      movq (ind ~ofs:offset rbp) (reg rax)
  | TEdot (expr, field) ->
      gen_expr frame expr ++
      addq (imm field.f_ofs) (reg rax) ++
      movq (ind rax) (reg rax)
  | TEassign (lhs_exprs, rhs_exprs) ->
      let lexpr = List.hd lhs_exprs in
      let rexpr = List.hd rhs_exprs in
      gen_laddr frame lexpr ++
      pushq (reg rax) ++
      gen_expr frame rexpr ++
      movq (reg rax) (reg rcx) ++
      popq rax ++
      movq (reg rcx) (ind rax) ++
      movq (reg rcx) (reg rax)
  | TEblock exprs ->
      let rec eval = function
        | [] -> movq (imm 0) (reg rax)
        | [expr] -> gen_expr frame expr
        | e::es -> gen_stmt frame e ++ eval es
      in
      eval exprs
  | TEprint exprs ->
      gen_print frame exprs
  | TEincdec (expr, op) ->
      gen_laddr frame expr ++
      pushq (reg rax) ++
      movq (ind rax) (reg rax) ++
      (match op with
       | Inc -> incq (reg rax)
       | Dec -> decq (reg rax)
      )++
      popq (rcx) ++
      movq (reg rax) (ind rcx)
  | _ ->
      failwith "Cannot handle this expression type"

and gen_laddr frame lexpr =
  match lexpr.expr_desc with
  | TEident var ->
      let offset =
        try Hashtbl.find frame.locals var.v_id
        with Not_found -> 
          try Hashtbl.find frame.params var.v_id
          with Not_found -> failwith ("Unknown variable: " ^ var.v_name)
      in
      leaq (ind ~ofs:offset rbp) rax
  | TEdot (expr, field) ->
      gen_expr frame expr ++
      addq (imm field.f_ofs) (reg rax)
  | TEunop (Ustar, expr) ->
      gen_expr frame expr
  | _ ->
      failwith "Invalid lvalue in assignment"

and gen_print frame exprs =
  let space_lbl = get_string_label " " in
  let fmt_s_lbl = get_string_label "%s" in

  let (code, _) = List.fold_left (fun (code, prev_was_string) expr ->
    let is_string = match expr.expr_typ with | Tstring -> true | _ -> false in
    
    let code = 
      if not prev_was_string && not is_string then
        code ++
        leaq (lab space_lbl) rsi ++
        leaq (lab fmt_s_lbl) rdi ++
        xorq (reg rax) (reg rax) ++
        call "printf_"
      else
        code
    in
    
    let code = match expr.expr_typ with
    | Tint ->
        let fmt_lbl = get_string_label "%ld" in
        code ++
        gen_expr frame expr ++
        movq (reg rax) (reg rsi) ++
        leaq (lab fmt_lbl) rdi ++
        xorq (reg rax) (reg rax) ++
        call "printf_"
    | Tbool ->
        let true_lbl = get_string_label "true" in
        let false_lbl = get_string_label "false" in
        let l_false = new_label () in
        let l_done = new_label () in
        code ++
        gen_expr frame expr ++
        testq (reg rax) (reg rax) ++
        je l_false ++
        leaq (lab true_lbl) rsi ++
        jmp l_done ++
        label l_false ++
        leaq (lab false_lbl) rsi ++
        label l_done ++
        leaq (lab fmt_s_lbl) rdi ++
        xorq (reg rax) (reg rax) ++
        call "printf_"
    | Tstring ->
        code ++
        gen_expr frame expr ++
        movq (reg rax) (reg rsi) ++
        leaq (lab fmt_s_lbl) rdi ++
        xorq (reg rax) (reg rax) ++
        call "printf_"
    | Tptr _ | Tnil | Tstruct _ ->
        let nil_lbl = get_string_label "<nil>" in
        let fmt_p_lbl = get_string_label "%p" in
        let l_nil = new_label () in
        let l_done = new_label () in
        code ++
        gen_expr frame expr ++
        testq (reg rax) (reg rax) ++
        je l_nil ++
        movq (reg rax) (reg rsi) ++
        leaq (lab fmt_p_lbl) rdi ++
        xorq (reg rax) (reg rax) ++
        call "printf_" ++
        jmp l_done ++
        label l_nil ++
        leaq (lab nil_lbl) rsi ++
        leaq (lab fmt_s_lbl) rdi ++
        xorq (reg rax) (reg rax) ++
        call "printf_" ++
        label l_done
    | _ ->
        code
    in
    (code, is_string)
  ) (nop, true) exprs  (* Start with true = no space before first arg *)
  in
  code

(* NOTE: statement generation *)

and gen_stmt frame s = match s.expr_desc with
  | TEvars vars ->
      List.fold_left (fun code v ->
        let offset = frame.stack_offset in
        Hashtbl.add frame.locals v.v_id offset;
        frame.stack_offset <- offset - 8;

        let init =
          match v.v_typ with
          | Tstring ->
              let empty_lbl = get_string_label "" in
              leaq (lab empty_lbl) rax ++
              movq (reg rax) (ind ~ofs:offset rbp)
          | _ ->
              movq (imm 0) (ind ~ofs:offset rbp)
        in

        code ++
        subq (imm 8) (reg rsp) ++
        init
      ) nop vars
  | TEif (cond, then_, else_) ->
      let end_label = new_label () in
      gen_expr frame cond ++
      testq (reg rax) (reg rax) ++
      (
        match else_.expr_desc with
        | TEskip ->
            je end_label ++
            gen_stmt frame then_
        | _ ->
            let else_label = new_label () in
            je else_label ++
            gen_stmt frame then_ ++
            jmp end_label ++
            label else_label ++
            gen_stmt frame else_
      ) ++
      label end_label
  | TEreturn exprs ->
      begin match exprs with
      | [] ->
          movq (reg rbp) (reg rsp) ++
          popq rbp ++
          ret
      | [expr] ->
          gen_expr frame expr ++
          movq (reg rbp) (reg rsp) ++
          popq rbp ++
          ret
      | _ ->
          failwith "Multiple Returns Not Supported";
      end
  | TEblock exprs ->
      List.fold_left (fun code s ->
        code ++ gen_stmt frame s
      ) nop exprs
  | TEfor (cond, body) ->
      let loop_start = new_label () in
      let loop_end = new_label () in
      label loop_start ++
      gen_expr frame cond ++
      testq (reg rax) (reg rax) ++
      je loop_end ++
      gen_stmt frame body ++
      jmp loop_start ++
      label loop_end
  | _ ->
      gen_expr frame s

(* NOTE: function generation *)

let function_ asm_name (f, body) =
  let frame = new_frame () in

  let param_offset = ref 16 in
  List.iter (fun v ->
    Hashtbl.add frame.params v.v_id !param_offset;
    param_offset := !param_offset + 8
  ) f.fn_params;

  label asm_name ++
  pushq (reg rbp) ++
  movq (reg rsp) (reg rbp) ++

  gen_stmt frame body ++

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
      | TDstruct _ -> code
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
