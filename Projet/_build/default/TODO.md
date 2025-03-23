liste des tache à faire

## Fichiers à modifier
- verif.ml
- evaluateur.ml

## Role et description des fichiers
`eval.ml`: ?
`evaluateur.ml`:?
`lexer.mll`: analyseur lexical
`parseur.mly`:analyseur synthaxique
`synthax.ml`: définition des types
`verif.ml`: vérification de type

## Commandes de compiliation et d'execution
`dune build`

`dune exec -- ./eval.exe file_name`

 
## Synthaxe du langage
appelle de fonction: f(x), ou x est le nom de la variable et f le nom de la fonction
déclaration de variable: let (x : σ) = M in N qui définit dans N une variable x de type σ valant la valeur résultant de M.
déclaration de fonction:let f(x1 : σ1, . . . , xn : σn) :  τ = M
 - xi est le nom de la variable.
 -  σi est le type.
 - τ est le type de retour
 - M est une expression qui produit un type τ