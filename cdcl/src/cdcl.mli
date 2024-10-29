(** Signature for a SAT solver. *)
module type SOLVER_CDCL = sig

    (** solve takes a cnf formula and returns either None if it is unsatisfiable or
        a model that satisfies the formula. *)
    val solve2 : Ast.t -> Ast.model option
  end

(** CDCL is a SAT solver parameterized by a choice function. *)
module CDCL(C:Dpll.CHOICE) : SOLVER_CDCL