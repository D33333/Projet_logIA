(** CDCL is a SAT solver parameterized by a choice function. *)
module CDCL(C:Dpll.CHOICE) : Dpll.SOLVER