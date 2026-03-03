
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

let rec expr frame e = match e.expr_desc with
  | TEconstant (Cint i) ->
      movq (imm64 i) (reg rax)
  | TEconstant (Cbool b) ->
      movq (imm (if b then 1 else 0)) (reg rax)
  | TEconstant (Cstring s) ->
      let lbl = get_string_label s in
      leaq (lab lbl) rax
  | TEprint el ->
      print_exprs frame el
  | _ ->
      nop (* TODO: continue implementation *)

and print_exprs frame el =
  List.fold_left (fun code e ->
    (* Evaluate expression to %rax *)
    code ++
    expr frame e ++
    (* Push argument for printf *)
    pushq (reg rax) ++
    (* Get format string - for now assume int *)
    leaq (lab (get_string_label "%d\n")) rax ++
    pushq (reg rax) ++
    xorq (reg rax) (reg rax) ++  (* clear %rax for variadic function *)
    call "printf_" ++
    addq (imm 16) (reg rsp)      (* clean up stack *)
  ) nop el

(* NOTE: statement generation *)

let rec stmt frame s = match s.expr_desc with
  | TEblock bl ->
      List.fold_left (fun code s -> code ++ stmt frame s) nop bl
  | TEprint el ->
      print_exprs frame el
  | _ -> nop (* TODO: continue implementation *)

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
  stmt frame body ++
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
