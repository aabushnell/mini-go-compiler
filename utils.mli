open Ast
open Tast

val string_of_ptyp : ptyp -> string
(** Convert a type to its string representation *)

val check_duplicates :
  get_key:('a -> 'b) -> on_duplicate:('a -> 'a -> unit) -> 'a list -> unit
(** Check for duplicates in a list
    @param get_key Function to extract key from element
    @param on_duplicate Callback invoked with (first_occurrence, duplicate)
    @param list The list to check for duplicates *)

val string_of_binop : binop -> string
val string_of_typ : typ -> string
val types_equal : typ -> typ -> bool
