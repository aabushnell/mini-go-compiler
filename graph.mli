(** Dependency graph utilities for structure definitions *)

open Ast

module StringSet : Set.S with type elt = string

(** Extract direct struct dependencies from a structure (non-pointer fields only) *)
val get_struct_dependencies : pstruct -> StringSet.t

(** Build dependency graph mapping struct names to their dependencies *)
val build_graph : pstruct list -> (string, StringSet.t) Hashtbl.t

(** Detect cycles in the dependency graph, returns list of cycle descriptions *)
val detect_cycles : pstruct list -> (string, StringSet.t) Hashtbl.t -> string list