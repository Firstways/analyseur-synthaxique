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


(* Recherche une variable parmis le type_env 
Si celle ci est trouvé alors retourne le type de celle ci *)
(* let recherche_variable_in_type_env variable type_env = 
  match type_env with 
    | [] ->  *)


(*Que font les fonctions*)
(* vérifie qu'une expression à un type donné *)
(* on vérifie que les données de l'expression corresponde au donnes du env type *)
(*  expr -> typ -> bool*)

(* let verif_expr expr t env_type env_fonction= true *)
let rec verif_expr (expr:expr) (type_env:env_type) = match expr with
| Var _ -> None
| IdFun _  ->  None
| Int _ ->  Some TInt
| Bool _ -> Some TBool
| BinaryOp (op, y, z) ->
  (match verif_bin_op op, verif_expr y type_env, verif_expr z type_env with
   | Some TInt, Some TInt, Some TInt -> Some TInt  (* Opérations arithmétiques *)
   | Some TBool, Some TBool, Some TBool -> Some TBool  (* Comparaisons *)
   | _ -> None)
| UnaryOp (op, z) ->
  (match verif_un_op op, verif_expr z type_env with
   | Some TInt, Some TInt -> Some TInt
   | Some TBool, Some TBool -> Some TBool
   | _ -> None)

| If (x, y, z) ->
  (match verif_expr x type_env, verif_expr y type_env, verif_expr z type_env with
   | Some TBool, Some ty1, Some ty2 -> if ty1 = ty2 then Some ty1 else None
   | _ -> None)

| Let (idvar, typ, expr1, expr2) ->
                if (verif_expr expr1 ((idvar,typ)::type_env) = Some typ) && verif_id_var idvar && verif_type_retour typ then
                  verif_expr expr2 type_env
                else None

| App (f, args) -> 
    if verif_id_fun f && verif_var_list args then Some TInt (* Supposons que les fonctions renvoient un int *)
    else None
| _ -> failwith ""

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

