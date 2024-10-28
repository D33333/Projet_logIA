open Dpll

module CDCL (C:CHOICE) : SOLVER =
  struct
    module S = DPLL(C)
    type answer = Sat of Ast.model | Unsat of Ast.Clause.t

    type history = (Ast.lit * (Ast.lit list) * int) list
    type instance = {
      ast : Ast.lab_t;
      assignment : Ast.model;
      unbound : S.LitSet.t;
      decisions : history;
      dl : int
    }

    let label (f : Ast.t) : Ast.lab_t =
      let rec label_aux (elts : Ast.Clause.t list) (acc : int) : Ast.Lab_Cnf.t =
        match elts with
          | [] -> Ast.Lab_Cnf.empty
          | clause::t -> Ast.Lab_Cnf.add ({c = clause; label = acc}) (label_aux t (acc+1))
      in
        {
          nb_var_l = f.nb_var;
          nb_clause_l = f.nb_clause;
          cnf_l = label_aux (Ast.Cnf.elements f.cnf) 0
        }

    let new_dl (instance : instance) (predecessors : Ast.lit list) : int = 
      match predecessors with 
        | [] -> instance.dl + 1
        | _ -> instance.dl

    let assign_literal (instance : instance) (literal : Ast.lit) (predecessors : Ast.lit list) : instance =
      let dl' = new_dl instance predecessors in
      let cnf =

        let assign_clause (clause: lab_clause) (cnf: Ast.Lab_Cnf.t) = (* a modifier *)
          if Ast.Clause.mem literal clause.c then cnf
          else Ast.Cnf.add ({c = Ast.Clause.remove (Ast.neg literal) clause.c ; label = clause.label}) cnf
        in Ast.Cnf.fold assign_clause instance.ast.cnf_l Ast.Lab_Cnf.empty in
      { ast = { instance.ast with cnf };

        assignment = literal :: instance.assignment;
        unbound = LitSet.remove (abs literal) instance.unbound;
        decisions = (literal,predecessors,dl')::instance.decisions;
        dl = dl'
      }

    let make_decision (instance : instance) : instance =
      let literal = LitSet.choose instance.unbound in
      assign_literal instance literal []

    let unit_propagate (instance : instance) : (Ast.lit * int) list =
      (* Récupère les littéraux pouvant faire une unit propagation et le label de leur clause *)
      let unit_clauses = Ast.Lab_Cnf.filter (fun clause -> (Ast.Clause.cardinal clause.c) == 1 instance.ast.cnf_l
      in Ast.Lab_Cnf.fold (fun clause l -> (Ast.Clause.min_elt clause.c,clause.label)::l) unit_clauses []
    
    let rec construct_predecessors_unit (unit_clauses : (Ast.lit * int) list) (original : instance) : (Ast.lit * (Ast.lit list) list) =
      (* remplace le label de la clause par la liste des prédecesseurs dans le graphe d'implication *)
      match unit_clauses with
      | [] -> []
      | (literal,label)::t ->
        let clause = Ast.Lab_Cnf.min_elt (Ast.Lab_Cnf.filter (fun clause -> clause.label == label) instance.ast.cnf_l)
        in List.map Ast.neg Ast.Clause.elements (Ast.Clause.remove literal clause.c)
    
    (* A AJOUTER PLUS TARD

    let pure_literal (instance : instance) : Ast.model =
      let rec filter_pure_literal list =
        match list with
        | x :: y :: xs -> if x == -y then filter_pure_literal xs else x :: filter_pure_literal (y :: xs)
        | _ -> list
        in let lab_clause_union (lab_clause1 : lab_clause) (clause2 : Ast.Clause.t) : Ast.Clause.t = Ast.Clause.union lab_clause1.c clause2
        in filter_pure_literal (Ast.Clause.elements (Ast.Lab_Cnf.fold lab_clause_union instance.ast.cnf_l Ast.Clause.empty))

    let rec construct_predecessors_pure (m : Ast.model) (original : instance) : (lit * (lit list)) list =
      match m with
      | [] -> []
      | literal::t ->
        let clauses_with_neg = Ast.Lab_Cnf.filter (fun clause -> Ast.Clause.mem (Ast.neg lit) clause.c) original.ast.cnf_l
        in 
        *)

      let rec simplify (instance : instance) (original : instance) : instance =
        (* Check if there is a unit clause in formula or pure: Unit Propagation *)
        let rec simplify_aux instance original updates =
          match updates with
          | [] -> instance
          | (literal,predecessors)::t -> simplify_aux (assign_literal instance literal predecessors) original t)
        in  simplify (simplify_aux instance original (construct_predecessors (unit_propagate instance)))

        (* PURE LITERAL PAS IMPLEMENTE : je decommenterai quand ca le sera
        match construct_predecessors (unit_propagate instance) with
        | [] -> instance
          begin
            match pure_literal instance with
            | [] -> instance
            | _ -> simplify (List.fold_left assign_literal instance (pure_literal instance))
          end
        | literals -> simplify (List.fold_left assign_literal instance literals) *)


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
