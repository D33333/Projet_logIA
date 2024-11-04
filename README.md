# Projet_logIA
Projet d'Aspects Logiques de l'IA

Question 2 : CDCL on a les fontions solve simplify … numéros de ligne

Question 3 : 
   - literals are represented by integers : positive if the literal is positive, negative else.
   - clauses are labeled (type lab_clause) justifier...
   - partial models are in a stack (codée par une liste et l'opération pop = l'accès au premier élément, pus = ajout de l'élément en tête de liste)
 
Question 3.2 :
   - pure_literal et unit_propagation (utilisées par simplify) détectent si c'est une formule de Horn ou si c'est une formule à 2 variables
Non, contre-exemple :
non x1 v x2 → x1=0 et x2=0 
non x3 → x3 =0
x1 v x3 ----> faux

Dans notre implémentation :
Nous avons également implémenté plusieurs heuristiques pour CDCL
On préfère choisir un littéral dans une grande clause
On préfère choisir un littéral dans une petite clause : la plus rapide sur les exemples fournis.
Variante du choix par défaut qui peut choisir la négation d'une variable au lieu de la mettre à vrai.

À noter : On utilise des labels pour les clauses qui nous permettent de se souvenir de la clause initiale correspondante dans la formule quand on construit le graphe d'implication.