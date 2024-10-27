open Dpll
module CDCL (C:CHOICE) : SOLVER =
  struct
    module S = DPLL(C)
    type answer = Sat of Ast.model | Unsat of Ast.Clause.t
    type nodeHistory = Ast.lit * (Ast.Clause.t option) * int
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
      { 
        ast = { instance.ast with cnf };
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


    let f_false_under_m (instance : instance) : Boolean = Ast.Cnf.exists Ast.Clause.is_empty instance.ast.cnf
    (*let F_unassigned (instance : instance) : Boolean = Ast.Cnf.exists Ast.Clause.unassigned instance.ast.cnf*)
    let f_true_under_m (instance : instance) : Boolean = Ast.Cnf.for_all Ast.Clause.valid instance.ast.cnf
    let f_unassigned_under_m (instance : instance) : Boolean = !f_false_under_m(instance) && !(f_true_under_m(instance))
    
    let rec go_back_to (dl : int) (dstack : history ) : history = match dstack with
      | [] -> []
      | (lit,preds,dl')::reste -> if (dl' < dl) then go_back_to dl reste
      else (lit,preds,dl')::(go_back_to dl reste)

    let rec find_preds_of_empty (dstack : history) : nodeHistory = match dstack with
    | (lit, preds, dl)::reste -> 
    | _ -> failwith "There is no node in the stack."

    (*let analyzeConflict (instance : instance) : Clause,int = *)

    let solve (f : Ast.t) : answer = 
      let range = List.init f.nb_var (fun x -> x + 1) in
      let unbound_vars = List.fold_left (fun set x -> LitSet.add x set) LitSet.empty range in
      let instance = simplify { ast = f; assignment = []; unbound = unbound_vars; decision = []; dl = 0 } in
      
      let noAssignment = true in
      while (noAssignment) do

        (*Backtracking*)
        while (f_false_under_m instance) do
          if (instance.dl=0) then Unsat else
          let clauseToLearn,dl = analyzeConflict instance

          (*Backtrack*)
          instance.dl = dl
          (*instance.ast = ...
          instance.assignment = ...
          instance.unbound = ...*)
          instance.decisions = go_back_to dl instance.decisions

          (*Clause Learning*)
          f.nb_clause+=1
          f.cnf = Cnf.of_list [f.cnf,Cnf.singleton(clauseToLearn)]
          instance = simplify instance
          done
        
        (*Boolean Decision*)
        if (f_unassigned_under_m instance) then {
          (*instance.decisions = ???*)
          instance.dl+=1
          instance.assignment = make_decision(instance)
          instance = simplify instance
        }
        noAssignment = f_unassigned_under_m instance || f_false_under_m instance
        done
    end
