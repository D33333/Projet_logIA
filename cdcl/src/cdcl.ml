module LitSet = Set.Make(struct type t = int let compare = compare end)
type history = (Ast.lit * (Ast.lit list) * int) list
type instance = {
    mutable ast : Ast.lab_t; (*the formula*)
    mutable assignment : Ast.model;
    mutable unbound : LitSet.t; (*unbound variables*)
    mutable decisions : history; (*corresponds to the dstack*)
    mutable dl : int; (*decision level*)
    mutable oldFormulas : (int * Ast.Lab_Cnf.t) list (*used to backtrack*)
}

(*-----------------------------------------------------------------------------------------------------------------*)
(* HEURISTIQUES DE DECISION *)
(*-----------------------------------------------------------------------------------------------------------------*)

module type CHOICE = sig
  val choice : instance -> Ast.lit
end

module DefaultChoice : CHOICE = 
struct
  let choice instance = LitSet.choose instance.unbound
end

module ImprovedDefaultChoice : CHOICE =
struct
  let choice instance =
    let var = LitSet.choose instance.unbound in
    let clauses_with_pos = Ast.Lab_Cnf.filter (fun clause -> Ast.Clause.mem var clause.c) instance.ast.cnf_l in
    let clauses_with_neg = Ast.Lab_Cnf.filter (fun clause -> Ast.Clause.mem (Ast.neg var) clause.c) instance.ast.cnf_l in
    if (Ast.Lab_Cnf.cardinal clauses_with_pos) < (Ast.Lab_Cnf.cardinal clauses_with_neg) then (Ast.neg var)
    else var
end

module ChooseSmallClause : CHOICE =
struct
  let choice instance =
    let smallest_clause = Ast.Lab_Cnf.min_elt instance.ast.cnf_l
    in Ast.Clause.choose smallest_clause.c
end

module ChooseLargeClause : CHOICE =
struct
  let choice instance =
    let largest_clause = Ast.Lab_Cnf.max_elt instance.ast.cnf_l
    in Ast.Clause.choose largest_clause.c
end

module CDCL (C:CHOICE) : Dpll.SOLVER =
  struct
    (*-----------------------------------------------------------------------------------------------------------------*)
    (* FONCTIONS POUR LE LABELLING *)
    (*-----------------------------------------------------------------------------------------------------------------*)
    let label (f : Ast.t) : Ast.lab_t =
      (*Renvoie une formule CNF labellisée à partir d'une formule CNF normale*)
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
    
    (*-----------------------------------------------------------------------------------------------------------------*)
    (* FONCTIONS UNITAIRES *)
    (*-----------------------------------------------------------------------------------------------------------------*)
    let contains_pos_lit (clause : Ast.lab_clause) : bool = Ast.Clause.exists (fun x->x>0) clause.c
    let contains_neg_lit (clause : Ast.lab_clause) : bool = Ast.Clause.exists (fun x->x<0) clause.c

    let new_dl (instance : instance) (predecessors : Ast.lit list) : int = 
      match predecessors with 
        | [] -> instance.dl + 1
        | _ -> instance.dl

    let max (x:int) (y:int) : int = if (x>y) then x else y

    let f_false_under_m (instance : instance) : bool = Ast.Lab_Cnf.exists (fun clauseL -> Ast.Clause.is_empty clauseL.c) instance.ast.cnf_l
    let f_true_under_m (instance : instance) : bool = (Ast.Lab_Cnf.for_all contains_pos_lit instance.ast.cnf_l)||(Ast.Lab_Cnf.for_all contains_neg_lit instance.ast.cnf_l)
    let f_unassigned_under_m (instance : instance) : bool = not(f_false_under_m instance) && not(f_true_under_m instance)

    let get_model (instance : instance) : Ast.model =
      let unbound_var = LitSet.elements instance.unbound in
      if (Ast.Lab_Cnf.for_all contains_pos_lit instance.ast.cnf_l) then unbound_var @ instance.assignment
      else (List.map (Ast.neg) unbound_var) @ (instance.assignment)

    let rec contains_literal (dstack : history) (literal : Ast.lit) : bool = match dstack with
    (*Renvoie vrai si le litéral est dans la dstack*)
    | [] -> false
    | (x,_,_)::reste -> (x=literal) || (contains_literal reste literal)

    let rec update_model (dstack : history) : Ast.model = match dstack with
    (*Reconstruit le modèle à partir de la dstack [surtout lorsqu'on fait un backtrack]*)
    | [] -> []
    | (lit, preds, dl)::reste -> lit::(update_model reste)

    let rec findMaxDl (preds : Ast.lit list) (dstack : history) : int = match dstack with
    (*Trouve le dl maximal parmi les littéraux de la liste preds grâce à la dstack*)
    | [] -> 0
    | (lit, predecessors, dl)::reste -> let maxOldDl = findMaxDl preds reste in
      if (List.mem lit preds) then max dl maxOldDl
      else maxOldDl

    let rec max_vars (clause : int list) : int = match clause with
    (*Renvoie le littéral d'indice maximal de la clause*)
    | [] -> 0
    | lit::autres -> let max = max_vars autres in if ((abs lit) > max) then (abs lit)
    else max
    
    let rec count_vars (formula : Ast.lab_clause list) : int = match formula with
    | [] -> 0
    | clause::reste -> let max1 = max_vars (Ast.Clause.elements clause.c) in
    let max2 = count_vars reste in if (max1 > max2) then max1
    else max2
    
    let rec find_old_formula (dl : int) (oldFormulas : (int * Ast.Lab_Cnf.t) list) : Ast.lab_t = match oldFormulas with
    (*Retrouve la formule au niveau de décision dl*)
    | [] -> failwith "Invalid level of decision"
    | (dl', formula)::reste -> if (dl' = dl) then 
      {
        nb_var_l = count_vars (Ast.Lab_Cnf.elements formula);
        nb_clause_l = Ast.Lab_Cnf.cardinal formula;
        cnf_l = formula
      }
    else find_old_formula dl reste

    let add (formula : Ast.lab_t) (clause : Ast.lab_clause) : Ast.lab_t = 
      (*Ajoute une clause à une formule [pour le clause learning]*)
      {
        nb_var_l = formula.nb_var_l;
        nb_clause_l = formula.nb_clause_l + 1 ;
        cnf_l = Ast.Lab_Cnf.add clause formula.cnf_l
      }
    
    (*-----------------------------------------------------------------------------------------------------------------*)
    (* FONCTIONS D'ACTION DE L'ALGORITHME *)
    (*-----------------------------------------------------------------------------------------------------------------*)
    let assign_literal (instance : instance) (literal : Ast.lit) (predecessors : Ast.lit list) : instance =
      let dl' = new_dl instance predecessors in
      let cnf =
        let assign_clause (clause: Ast.lab_clause) (cnf: Ast.Lab_Cnf.t) =
          if Ast.Clause.mem literal clause.c then cnf
          else Ast.Lab_Cnf.add ({c = Ast.Clause.remove (Ast.neg literal) clause.c ; label = clause.label}) cnf
        in Ast.Lab_Cnf.fold assign_clause instance.ast.cnf_l Ast.Lab_Cnf.empty in
      let new_ast : Ast.lab_t = {cnf_l = cnf ; nb_clause_l = instance.ast.nb_clause_l ; nb_var_l = instance.ast.nb_var_l} in
      { 
        ast = new_ast;
        assignment = literal :: instance.assignment;
        unbound = LitSet.remove (abs literal) instance.unbound;
        decisions = (literal,predecessors,dl')::instance.decisions;
        dl = dl';
        oldFormulas = (instance.dl,instance.ast.cnf_l)::instance.oldFormulas
      }

    let make_decision (instance : instance) : instance =
      let literal = C.choice instance in
      assign_literal instance literal []

    let get_unit_clauses (instance : instance) : (Ast.lit * int) list =
      (* Récupère les littéraux pouvant faire une unit propagation et le label de leur clause *)
      let unit_clauses = Ast.Lab_Cnf.filter (fun clause -> (Ast.Clause.cardinal clause.c) == 1) instance.ast.cnf_l
      in Ast.Lab_Cnf.fold (fun clause l -> (Ast.Clause.min_elt clause.c,clause.label)::l) unit_clauses []
    
    let rec construct_predecessors_unit (unit_clauses : (Ast.lit * int) list) (original : Ast.lab_t) : (Ast.lit * (Ast.lit list)) list =
      (* Remplace le label de la clause par la liste des prédecesseurs dans le graphe d'implication (littéraux de la clause assignés auparavant) *)
      match unit_clauses with
      | [] -> []
      | (literal,label)::t ->
        let clause = Ast.Lab_Cnf.min_elt (Ast.Lab_Cnf.filter (fun clause -> clause.label == label) original.cnf_l)
        in let pred = List.map Ast.neg (Ast.Clause.elements (Ast.Clause.remove literal clause.c))
        in (literal,pred)::(construct_predecessors_unit t original)

    let unit_propagate (instance : instance) (original : Ast.lab_t) : (Ast.lit * (Ast.lit list)) list =
      construct_predecessors_unit (get_unit_clauses instance) original

    let pure_literals (instance : instance) : Ast.model =
      let rec filter_pure_literal list =
        match list with
        | x :: y :: xs -> if x == -y then filter_pure_literal xs else x :: filter_pure_literal (y :: xs)
        | _ -> list
        in let lab_clause_union (l_clause : Ast.lab_clause) = Ast.Clause.union l_clause.c
        in filter_pure_literal (Ast.Clause.elements (Ast.Lab_Cnf.fold lab_clause_union instance.ast.cnf_l Ast.Clause.empty))

    let assign_pure_literals (instance : instance) (literals : Ast.lit list) : instance =
      let rec without_pure_literal (clause : int list) (literals : Ast.lit list) : bool =
        match clause, literals with
        | [],_ -> true
        | _,[] -> true
        | l1::t1,l2::t2 when l1=l2 -> false
        | l1::t1,l2::t2 when (abs l1)<(abs l2) -> without_pure_literal t1 literals
        | l1::t1,l2::t2 -> without_pure_literal clause t2
      in 
      {
        ast = {
          cnf_l = Ast.Lab_Cnf.filter (fun clause -> without_pure_literal (Ast.Clause.elements clause.c) literals) (instance.ast.cnf_l);
          nb_clause_l = instance.ast.nb_clause_l;
          nb_var_l = instance.ast.nb_var_l
        } ;
        assignment = instance.assignment @ literals;
        unbound = LitSet.union (instance.unbound) (LitSet.of_list literals) ;
        decisions = instance.decisions;
        dl = instance.dl;
        oldFormulas = instance.oldFormulas
      }

    let rec simplify (instance : instance) (original : Ast.lab_t) : instance =
      match unit_propagate instance original with
      | [] ->
        begin
        match pure_literals instance with
        | [] -> instance
        | literals -> simplify (assign_pure_literals instance literals) original
        end
      | assignments -> 
        let assign_unit (i : instance) ((l,pred) : Ast.lit * (Ast.lit list)) : instance = assign_literal i l pred in
        simplify (List.fold_left assign_unit instance assignments) original
    
    let rec go_back_to (dl : int) (dstack : history) (unbound : LitSet.t) : history * LitSet.t =
      (*Effectue le backtrack au niveau dl et met à jour les variables non assignées (unbound)*)
      match dstack with
      | [] -> [],unbound
      | (lit,preds,dl')::reste -> let dstack',unbound' = go_back_to dl reste unbound in
      if (dl' > dl) then dstack',(LitSet.add lit unbound')
      else (lit,preds,dl')::dstack',unbound'

    let rec find_preds_of_bottom (dstack : history) : (Ast.lit list) =
      match dstack with
      | (0, preds, -1)::reste -> preds (*Noeud bottom => clause vide*)
      | (lit, preds, dl)::reste -> find_preds_of_bottom reste (*On cherche bottom*)
      | _ -> failwith "There is no empty clause in the stack."

    let rec findPreds (literal : Ast.lit) (dstack : history) : (Ast.lit list) =
      (*Remonte dans le graphe d'implication pour trouver les noeuds sans prédécesseurs en partant de "literal"*)
      match dstack with
      | [] -> []
      | (lit, preds, dl)::reste -> if (literal=lit) then 
        let rec findPredsPreds (predecessors : Ast.lit list) = match predecessors with
          | [] -> literal::[]
          | pred::autres -> let predLit = findPreds pred dstack in 
            let predsLit = findPredsPreds autres in predLit @ predsLit in
            findPredsPreds preds
        else findPreds literal reste

    let rec findParentConflict (conflictLit : Ast.lit list) (dstack : history) : (Ast.lit list) =
      (*Trouve les prédécesseurs de chaque littéral dans conflictLit*)
      match conflictLit with
    | [] -> []
    | lit::reste -> (findPreds lit dstack) @ (findParentConflict reste dstack)

    let analyzeConflict (instance : instance) : Ast.lab_clause * int = 
      let predsBottom = find_preds_of_bottom instance.decisions in
      match predsBottom with
      | lit::reste -> let conflict = findParentConflict (lit::reste) instance.decisions in (*on obtient une liste de littéraux négatifs (ce sont des et entre eux)*)
        let maxDl = findMaxDl conflict instance.decisions in
        let rec createClauseToLearn (conflit : Ast.lit list) : Ast.lab_clause = match conflit with
          | [] -> {c = Ast.Clause.empty; label = instance.ast.nb_clause_l}
          | lit::reste -> let clauseToLearn = createClauseToLearn reste in {c = Ast.Clause.add (Ast.neg lit) (clauseToLearn.c); label = clauseToLearn.label} in (*A RELIRE*)
        (createClauseToLearn conflict),maxDl
      | _ ->  failwith "Error in the implication graph"

    (*-----------------------------------------------------------------------------------------------------------------*)
    (* FONCTION SOLVE DE CDCL *)
    (*-----------------------------------------------------------------------------------------------------------------*)
    let solve (formulaInit : Ast.t) : Ast.model option =
      let fInit = label formulaInit in
      let range = List.init formulaInit.nb_var (fun x -> x + 1) in
      let unbound_vars = LitSet.of_list range in
      let instance = ref (simplify { ast = fInit; assignment = []; unbound = unbound_vars; decisions = []; dl = 0; oldFormulas = [] } fInit) in

      let noAssignment = ref true in
      let isUnsat = ref false in

      while (!noAssignment && not (!isUnsat)) do

        (*Backtracking*)
        while (f_false_under_m !instance && not (!isUnsat)) do
          isUnsat := (!instance.dl=0);
          if (!isUnsat) then () else
          let clauseToLearn,dl = analyzeConflict !instance in

          (*Backtrack*)
          !instance.dl <- dl;
          let decisions',unbound' = go_back_to dl !instance.decisions !instance.unbound in
          !instance.decisions <- decisions';
          !instance.unbound <- unbound';
          !instance.assignment <- update_model !instance.decisions;
          !instance.ast <- find_old_formula dl !instance.oldFormulas;

          (*Clause Learning*)
          !instance.ast <- add !instance.ast clauseToLearn;
          instance := simplify !instance fInit;
        done;

        (*Boolean Decision*)
        if (f_unassigned_under_m !instance && not (!isUnsat)) then
          begin
          !instance.dl <- !instance.dl + 1;
          instance := make_decision(!instance);
          instance := simplify !instance fInit;
          end;
        
        noAssignment := not (f_true_under_m !instance)
      done;
      if (!isUnsat) then None else
      Some (get_model !instance)
    end