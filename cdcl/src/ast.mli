(** Type of variables in cnf formulas. *)
type var = int

(** We use the same type for litterals except we use negatives values. *)
type lit = int

(** Contains litterals that satisfy a cnf formula as returned by a SAT solver. *)
type model = int list

(** A set of variables *)
module Clause : Set.S with type elt = var
type lab_clause = {
  c: Clause.t;
  label: int
}

(** A set of clauses *)
module Cnf : Set.S with type elt = Clause.t
module Lab_Cnf : Set.S with type elt = lab_clause

(** A cnf problem *)
type t =
  {
    nb_var : int; (** number of variables *)
    nb_clause : int; (** number of clauses *)
    cnf : Cnf.t (** the cnf formula *)
  }

type lab_t =
  {
    mutable nb_var_l: int;
    mutable nb_clause_l: int;
    mutable cnf_l: Lab_Cnf.t
  }

(** [neg v] returns the opposite litteral *)
val neg : lit -> lit

type 'a printer = Format.formatter -> 'a -> unit

(** [pp_clause fmt cl] prints a clause *)
val pp_clause : Clause.t printer

(** [pp_cnf fmt cnf] prints a cnf *)
val pp_cnf : Cnf.t printer

(** [pp fmt ast] prints an ast (problem) *)
val pp : t printer
