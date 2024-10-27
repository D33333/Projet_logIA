open Dpll
module CDCL (C:CHOICE) : SOLVER =
  struct
    module S = DPLL(C)
    type answer = Sat of Ast.model | Unsat of Ast.Clause.t
    type history = (Ast.lit * (Ast.Clause.t option) * int) list
    type instance = {
      ast : Ast.t;
      assignment : Ast.model;
      unbound : S.LitSet.t;
      decisions : history; (* dstack *)
      dl : int
    }

    let new_dl (instance : instance) (clause : Ast.Clause.t option) : int = 
      match clause with 
        | None -> instance.dl + 1
        | _ -> instance.dl

    let assign_literal (instance : instance) (literal : Ast.lit) (clause : Ast.Clause.t option) : instance =
      (* Construct a new CNF without the literal *)
      let dl' = new_dl instance clause in
      let cnf =
        let assign_clause (clause: Ast.Clause.t) (cnf: Ast.Cnf.t) =
          if Ast.Clause.mem literal clause then cnf
          else Ast.Cnf.add (Ast.Clause.remove (Ast.neg literal) clause) cnf
        in Ast.Cnf.fold assign_clause instance.ast.cnf Ast.Cnf.empty in
      { ast = { instance.ast with cnf };
        assignment = literal :: instance.assignment;
        unbound = LitSet.remove (abs literal) instance.unbound;
        decisions = (literal,clause,dl')::instance.decisions;
        dl = dl'
      }

    let make_decision (instance : instance) : instance =
      let literal = LitSet.choose instance.unbound in
      assign_literal instance literal None
    
      (* pour modifier la suite il faudrait avoir accès à la version originale de la formule *)

    let unit_propagate (instance : instance) : Ast.model =
      let unit_clause = Ast.Clause.fold (fun x y -> x :: y)
      in Ast.Cnf.fold unit_clause (Ast.Cnf.filter (fun clause -> (Ast.Clause.cardinal clause) == 1) instance.ast.cnf) []
    
      let pure_literal (instance : instance) : Ast.model =
        let rec filter_pure_literal list =
          match list with
          | x :: y :: xs -> if x == -y then filter_pure_literal xs else x :: filter_pure_literal (y :: xs)
          | _ -> list
        in filter_pure_literal (Ast.Clause.elements (Ast.Cnf.fold Ast.Clause.union instance.ast.cnf Ast.Clause.empty))

      let rec simplify (instance: instance): instance =
        (* Check if there is a unit clause in formula or pure: Unit Propagation *)
        match unit_propagate instance with
        | [] -> begin
            (* Check if there is a literal that occurs pure in formula *)
            match pure_literal instance with
            | [] -> instance
            | _ -> simplify (List.fold_left assign_literal instance (pure_literal instance))
          end
        | literals -> simplify (List.fold_left assign_literal instance literals)

    let rec solve_sat (instance : instance) : answer = 
    let solve (f : Ast.t) : Ast.model option =
  end
