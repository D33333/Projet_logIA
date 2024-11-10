# Projet_logIA
Projet d'Aspects Logiques de l'IA

Alban Mattei -- Diane Cauquil

Lien vers le Github du projet : https://github.com/D33333/Projet_logIA.git

Question 2 :
Dans cdcl.ml, les fonctions du cours ont bien été définies :
assign_literal : ligne 140, qui choisit la valeur à assigner à un littéral en fonction de l'heuristique donnée (équivalent à la fonction decide du cours)
unit_propagate : ligne 175
pure_literals : ligne 178
simplify : ligne 208, qui combine la propagation unitaire et détecte les littéraux purs.
analyse_conflict : ligne 252
solve : ligne 266

Question 3 : 
   - Les littéraux sont représentés par des entiers : positif si le littéral est positif, négatif sinon (ligne 3 dans ast.ml).
   - Les clauses ont une information supplémentaire : le label (ligne 29 dans ast.ml), qui sert pour le clause learning. Le label nous permet de nous souvenir à tout moment de la forme de la clause que l'on manipule dans la formule initiale quand on construit le graphe d'implication.
   Une clause non labelisée est représentée comme un ensemble de littéraux.
   - Les modèles partiels sont stockés dans une pile (codée par une liste et l'opération pop = l'accès au premier élément, pus = ajout de l'élément en tête de la liste) (ligne 5 dans cdcl.ml).
 
Question 3.2 :
   - Les fonctions pure_literal et unit_propagation (utilisées par simplify) détectent si la formule est composée de clauses de Horn.
   - Non, contre-exemple :
      Soit la formule f = (non x1 v x2) et (non x3) et (x1 v x3)

      En détectant que les 2 premières clauses sont de Horn, on obtient le modèle :
      non x1 v x2 → x1=0 et x2=0
      non x3 → x3=0
      Modèle : x1=0, x2=0, x3=0

      Pourtant ce n'est pas un modèle pour la dernière clause donc CDCL devra repartir du début. L'algorithme n'a donc pas gagné de temps.
      x1 v x3 --> faux

Dans notre implémentation :
   - Nous avons également implémenté plusieurs heuristiques pour CDCL
      - Heuristique 1 : On préfère choisir un littéral dans une grande clause
      - Heuristique 2 : On préfère choisir un littéral dans une petite clause : la plus rapide sur les exemples fournis.
      - Heuristique 3 : Variante du choix par défaut qui peut choisir la négation d'une variable au lieu de la mettre à vrai.