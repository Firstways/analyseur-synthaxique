(* Belouin Eliot & Boyenval Louis-Marie*)
open Syntax

let verif_main _main = failwith""

let verif_id_fun (id : idfun) = id <> "" 

let verif_id_var (id : idvar) = id <> "" 


let verif_var_list var_list =match var_list with
| [] -> true
|_::_ -> true
(* |_ -> false  *)

let verif_type_retour type_retour = match type_retour with
|TInt -> true
|TBool -> true
(* | _ -> false *)

 


let  verif_bin_op op  = match op with
  | Plus ->true 
  | Minus -> true
  | Mult -> true
  | Div -> true
  | And -> true
  | Or -> true
  | Equal ->true
  | NEqual -> true
  | Less -> true
  | LessEq -> true
  | Great -> true
  | GreatEq -> true

let verif_un_op op = match op with
| Not -> true
(* | _ -> false  *)



(*Que font les fonctions*)
(* vérifie qu'une expression à un type donné *)
(* on vérifie que les données de l'expression corresponde au donnes du env type *)
(*  expr -> typ -> bool*)

(* let verif_expr expr t env_type env_fonction= true *)
let rec verif_expr (expr:expr) = match expr with
| Var _ -> true
| IdFun _  ->  true
| Int _ ->  true
| Bool _ -> true
| BinaryOp (op,y,z)->  (verif_bin_op op) && (verif_expr y) && (verif_expr z)
| UnaryOp (op,z)-> (verif_un_op op) && verif_expr z
| If (x,y,z)-> (verif_expr x) && (verif_expr y) &&  (verif_expr z)
| Let (idvar, typ, expr1, expr2)-> (verif_expr expr1)  && (verif_expr expr2) && verif_id_var idvar && verif_type_retour typ
| App (f,args) -> verif_id_fun f && verif_var_list args




(* vérifie que la déclaration des fonctions est correcte *)
(* une fonction c'est 
un nom 
un type de retour
une liste d'arguments
et une expression  *)
(*  idfun ->  bool*)
let verif_decl_fun (fonction: fun_decl) =
  (verif_id_fun fonction.id)
  && (verif_var_list fonction.var_list)
  && (verif_type_retour fonction.typ_retour)
  && (verif_expr fonction.corps)


let rec verif_main_in_env_fun env_fun = match env_fun with 
  |[]->false
  |(k,_)::y-> k = "main" || verif_main_in_env_fun y
(* retourne vrai si le programme est bien typé sinon faux *)
(*  'programme -> bool *)
let  verif_prog (simpleML:programme) = 
  let rec aux (p:programme) (env_fun:env_fonction)=
    match p with
      | [] -> verif_main_in_env_fun env_fun
      | x::y -> verif_decl_fun x && aux y ((x.id,x.typ_retour)::env_fun)
  in aux simpleML []



(* type utilisé pour vérifie le typage  *)
(* au début nous avons une liste vide
dès qu'une variable est trouvé, on l'ajoute ainsi 
que son type  *)
(* Associe un type a une variable *)
type env_type = (idvar * typ) list



type valeur = TInt of int | TBool of bool

(* type utilisé pour vérifier l'évalution des expressions*)
(* Associe une valeur a une variable *)
type env_val = (idvar * valeur) list

type env_fun = (idfun * (typ list * typ)) list
