(* Belouin Eliot & Boyenval Louis-Marie*)

open Syntax
(*Que font les fonctions*)
(* vérifie qu'une expression à un type donné *)
(*  expr -> typ -> bool*)
let verif_expr expr t env_type env_fonction= failwith "Not yet implemented"


(* vérifie que la déclaration des fonctions est correcte *)
(*  idfun ->  bool*)
let verif_decl_fun fonction env_fonction = failwith "Not yet implemented"

(* retourne vrai si le programme est bien typé sinon faux *)
(*  'programme -> bool *)
let verif_prog simpleML = failwith "Not yet implemented"


(* type utilisé pour vérifie le typage  *)
(* au début nous avons une liste vide
dès qu'une variable est trouvé, on l'ajoute ainsi 
que son type  *)
(* Associe un type a une variable *)
type env_type = (idvar * typ) list

(* type utilisé pour vérifié l'évalution des expressions*)
(* Associe une valeur a une variable *)
type env_val = (idvar * valeur) list

type valeur = TInt of int | TBool of bool
