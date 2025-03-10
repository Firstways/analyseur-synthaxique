open Syntax
(*Que font les fonctions*)
(* vérifie qu'une expression à un type donné *)
(*  'expr -> 'b -> bool*)
let verif_expr expr t env_type= failwith "Not yet implemented"


(* vérifie que la déclaration des fonctions est correcte *)
(*  'fun_decl -> bool*)
let verif_decl_fun fonction = failwith "Not yet implemented"

(* retourne vrai si le programme est ien typé sinon faux *)
(*  'programme -> 'typ *)
let verif_prog simpleML = failwith "Not yet implemented"


(* type utilisé pour vérifie le typage  *)
(* au début nous avons une liste vide
dès qu'une variable est trouvé, on l'ajoute ainsi 
que son type  *)
(* Associe un type a une variable *)
type env_type = (idvar * typ) list

(* type utilisé pour vérifié l'évalution des expressions*)
(* Associe une valeur a une variable *)
type env_exp = (idfun * typ) list

