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

      let rec simplify (instance: instance) : instance =
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
    
    let rec go_back_to (dl : int) (dstack : history ) (unbound : S.LitSet.t) : history,S.LitSet.t = match dstack with
      | [] -> [],unbound
      | (lit,preds,dl')::reste -> let dstack',unbound' = go_back_to dl reste in
      if (dl' > dl) then dstack',(S.LitSet.add lit unbound')
      else (lit,preds,dl')::dstack',unbound'

    let rec find_preds_of_bottom (dstack : history) : Ast.Clause.t option = match dstack with
    | (0, preds, -1)::reste -> preds (*Noeud bottom => clause vide*)
    | (lit, preds, dl)::reste -> find_preds_of_bottom reste (*On cherche bottom*)
    | _ -> failwith "There is no empty clause in the stack."

    let rec contains_literal (dstack : history) (literal : lit) : Boolean = match dstack with
    | [] -> return false
    | x::reste -> (x=literal) || (contains_literal reste literal)
    
    (*let rec add (dstack : history) (dl : int) (assignment : Ast.model) : history = match assignment with
    | [] -> dstack
    | -1::reste -> (-1, ???, -1)::(add dstack dl reste)
    | literal::reste -> if (contains_literal dstack literal) then add dstack dl reste
    else (literal, ???, dl)::(add dstack dl reste)*)

    let rec remove (dstack : history) : Ast.model = match dstack with
    | [] -> []
    | (lit, preds, dl)::reste -> lit::(remove reste)

    let findParentConflict (conflictLit : lit list) (dstack : history) : (lit list),int = ...

    let analyzeConflict (instance : instance) : Clause,int = 
      let predsBottom = find_preds_of_bottom instance.decisions in
      match predsBottom with
      | lit::reste -> let conflict,maxDl = findParentConflict lit::reste instance.decisions in (*on obtient une liste de littéraux négatifs (ce sont des et entre eux)*)
        let rec createClauseToLearn conflit = match conflit with
          | [] -> Clause.empty
          | lit::reste -> Clause.add (Ast.neg lit) (createClauseToLearn reste) in
          (createClauseToLearn conflict),maxDl
      | _ ->  failwith "Error in the implication graph"

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
          instance.decisions,instance.unbound = go_back_to dl instance.decisions instance.unbound
          instance.assignment = remove instance.decisions
          instance.ast = (*Recup ce qu'il y a dans instance.decisions à ce niveau là*)

          (*Clause Learning*)
          f.nb_clause+=1
          f.cnf = Cnf.of_list [f.cnf,Cnf.singleton(clauseToLearn)]
          instance = simplify instance
          done
        
        (*Boolean Decision*)
        if (f_unassigned_under_m instance) then {
          instance.dl+=1
          instance = make_decision(instance)
          instance = simplify instance
        }
        noAssignment = f_unassigned_under_m instance || f_false_under_m instance
        done
    end
