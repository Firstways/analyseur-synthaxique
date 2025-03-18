(* Belouin Eliot & Boyenval Louis-Marie*)
open Syntax


let verif_id_fun (id : idfun) = id <> "" 

let verif_id_var (id : idvar) = id <> "" 


let verif_var_list var_list =match var_list with
(* on retourne faux si la liste est vide car
si il n'y a pas d'argument alors ce n'est pas une fonction *)
| [] -> false
|_::_ -> true
(* |_ -> false  *)

let verif_type_retour type_retour = match type_retour with
|TInt -> true
|TBool -> true
(* | _ -> false *)

 


let  verif_bin_op op  = match op with
  | Plus ->Some TInt 
  | Minus ->Some TInt 
  | Mult ->Some TInt 
  | Div ->Some TInt 
  | And ->Some TInt 
  | Or -> Some TBool 
  | Equal ->Some TBool 
  | NEqual -> Some TBool 
  | Less -> Some TInt 
  | LessEq -> Some TInt 
  | Great -> Some TInt 
  | GreatEq -> Some TInt 

let verif_un_op op = match op with
| Not -> Some TBool 


(*Que font les fonctions*)
(* vérifie qu'une expression à un type donné *)
(* on vérifie que les données de l'expression corresponde au donnes du env type *)
(*  expr -> typ -> bool*)

(* let verif_expr expr t env_type env_fonction= true *)
let rec verif_expr (expr:expr) = match expr with
| Var _ -> None
| IdFun _  ->  None
| Int _ ->  Some TInt
| Bool _ -> Some TBool
| BinaryOp (op, y, z) ->
  (match verif_bin_op op, verif_expr y, verif_expr z with
   | Some TInt, Some TInt, Some TInt -> Some TInt  (* Opérations arithmétiques *)
   | Some TBool, Some TBool, Some TBool -> Some TBool  (* Comparaisons *)
   | _ -> None)
| UnaryOp (op, z) ->
  (match verif_un_op op, verif_expr z with
   | Some TInt, Some TInt -> Some TInt
   | Some TBool, Some TBool -> Some TBool
   | _ -> None)
| If (x, y, z) ->
  (match verif_expr x, verif_expr y, verif_expr z with
   | Some TBool, Some ty1, Some ty2 when ty1 = ty2 -> Some ty1
   | _ -> None)

| Let (idvar, typ, expr1, expr2) ->
                if (verif_expr expr1 = Some typ) && verif_id_var idvar && verif_type_retour typ then
                  verif_expr expr2
                else None
| App (f, args) -> 
    if verif_id_fun f && verif_var_list args then Some TInt (* Supposons que les fonctions renvoient un int *)
    else None

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
  && match (verif_expr fonction.corps) with
      | None -> false
      | Some TInt-> true
      | Some TBool -> true


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
