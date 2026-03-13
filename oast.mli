
(** Optimized syntax trees **)

type unop = Ast.unop

type binop =
  | Badd | Bsub | Bmul | Bdiv | Bmod
  | Beq  | Bne  | Blt  | Ble  | Bgt  | Bge
  | Band | Bor
  | Bshl   (** new: arithmetic left shift *)
  | Bshr   (** new: arithmetic right shift *)

type constant  = Tast.constant

type incdec    = Tast.incdec

type function_ = Tast.function_

type structure = Tast.structure

type typ       = Tast.typ

type var       = Tast.var

type field     = Tast.field

type expr = { expr_desc : expr_desc; expr_typ : typ }

and expr_desc =
  | OEskip
  | OEconstant of constant
  | OEbinop    of binop * expr * expr
  | OEunop     of unop  * expr
  | OEnil
  | OEnew      of typ
  | OEcall     of function_ * expr list
  | OEident    of var
  | OEdot      of expr * field
  | OEassign   of expr * expr         (** single assignment ensured *)
  | OEvars     of var list
  | OEif       of expr * expr * expr
  | OEreturn   of expr option         (** one or zero returns ensured *)
  | OEblock    of expr list
  | OEfor      of expr * expr
  | OEprint    of expr list
  | OEincdec   of expr * incdec

type odecl =
  | ODfunction of function_ * expr
  | ODstruct   of structure

type ofile = odecl list
