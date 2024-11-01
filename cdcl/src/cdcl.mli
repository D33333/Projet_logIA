module LitSet : Set.S with type elt = int

type history = (Ast.lit * (Ast.lit list) * int) list
type instance = {
    mutable ast : Ast.lab_t;
    mutable assignment : Ast.model;
    mutable unbound : LitSet.t;
    mutable decisions : history;
    mutable dl : int;
    mutable oldFormulas : (int * Ast.Lab_Cnf.t) list (* (int * Ast.lab_t) list ? *)
  }

module type CHOICE = sig
  val choice : instance -> Ast.lit
end

module DefaultChoice : CHOICE
module ImprovedDefaultChoice : CHOICE
module ChooseSmallClause : CHOICE
module ChooseLargeClause : CHOICE

(** Signature for a SAT solver. *)
(** CDCL is a SAT solver parameterized by a choice function. *)
module CDCL(C:CHOICE) : Dpll.SOLVER