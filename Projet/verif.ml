(* Belouin Eliot & Boyenval Louis-Marie*)
open Syntax

(* il faut pour voir vérifier le type de la variable
ainsi il faut définir sont type lors de l'evaluation de l'expression
le pb étant de déterminer si c'est un 
TInt ou un TBool *)
let verif_id_fun (id : idfun) = id <> "" 

let verif_id_var (id : idvar) = id <> "" 


let verif_var_list var_list =match var_list with
(* on retourne faux si la liste est vide car
si il n'y a pas d'argument alors ce n'est pas une fonction *)
| [] -> true
|_::_ -> true
(* |_ -> false  *)

let verif_type_retour type_retour = match type_retour with
|TInt -> true
|TBool -> true
|TUnit -> true
(* | _ -> false *)

 


let  verif_bin_op op  = match op with
  | Plus | Minus | Mult | Div -> Some TInt 
  | And | Or -> Some TBool 
  | Equal | NEqual | Less | LessEq | Great | GreatEq -> Some TBool 


let verif_un_op op = match op with
| Not -> Some TBool 


(* Recherche une variable parmis le type_env 
Si celle ci est trouvé alors retourne le type de celle ci *)
let rec  recherche_variable_in_type_env variable (type_env) = 
  match type_env with 
    | [] -> None
    | (x,t)::y -> if x = variable then Some t else recherche_variable_in_type_env variable y

(*Que font les fonctions*)
(* vérifie qu'une expression à un type donné *)
(* on vérifie que les données de l'expression corresponde au donnes du env type *)
(*  expr -> typ -> bool*)

(* let verif_expr expr t env_type env_fonction= true *)
let rec verif_expr (expr:expr) (type_env:env_type) = match expr with
| Var x -> recherche_variable_in_type_env x type_env
| Int _ ->  Some TInt
| Bool _ -> Some TBool
| BinaryOp (op, y, z) ->
  (match verif_bin_op op, verif_expr y (type_env), verif_expr z type_env with
   | Some TInt, Some TInt, Some TInt -> Some TInt  (* Opérations arithmétiques *)
   | Some TBool, Some TBool, Some TBool -> Some TBool  (* Comparaisons *)
   | Some TBool, Some TInt, Some TInt -> Some TBool   
   | _ -> None)

| UnaryOp (op, z) ->
  (match verif_un_op op, verif_expr z type_env with
   | Some TBool, Some TBool -> Some TBool
   | _ -> None) 

  | If (x, y, z) ->
  (match verif_expr x type_env, verif_expr y type_env, verif_expr z type_env with
    | Some TBool, Some t1, Some t2 -> if t1 = t2 then  Some t1  else None
    | _ -> None)
  

| Let (idvar, typ, expr1, expr2) ->
  (match verif_expr expr1 type_env with
    | Some t when t = typ -> verif_expr expr2 ((idvar,typ)::type_env) 
    | _ -> None)
    

| App (f, _) -> 
  (match recherche_variable_in_type_env f type_env with
  | Some typ -> Some typ  (* ⚡ Récupère le vrai type *)
  | None -> None)

| _ -> failwith "nope"

(* vérifie que la déclaration des fonctions est correcte *)

(*  idfun ->  bool*)
let verif_decl_fun (fonction: fun_decl) (type_env:env_type) =
  (verif_id_fun fonction.id)
  && (verif_var_list fonction.var_list)
  && (verif_type_retour fonction.typ_retour)
  && match (verif_expr fonction.corps type_env) with
      | None -> false
      | Some _-> true


let rec verif_main_in_env_fun env_fun = match env_fun with 
  |[]->false
  |(k,_)::y-> k = "main" || verif_main_in_env_fun y
(* retourne vrai si le programme est bien typé sinon faux *)
(*  'programme -> bool *)
let  verif_prog (simpleML:programme) = 
  let rec aux (p:programme) (env_fun:env_fonction)=
    match p with
      | [] -> verif_main_in_env_fun env_fun
      | x::y -> verif_decl_fun x [] && aux y ((x.id,x.typ_retour)::env_fun)
  in aux simpleML []



type valeur = TInt of int | TBool of bool

(* type utilisé pour vérifier l'évalution des expressions*)
(* Associe une valeur a une variable *)
type env_val = (idvar * valeur) list

