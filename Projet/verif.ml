(* Belouin Eliot & Boyenval Louis-Marie 684i*)
open Syntax



(* il faut pour voir vérifier le type de la variable
ainsi il faut définir sont type lors de l'evaluation de l'expression
le pb étant de déterminer si c'est un TInt ou un TBool *)

(* Vérifie si un identifiant de fonction est valide (non vide) *)
(* idvar -> bool *)
let verif_id_fun (id : idfun) = id <> "" 

(* Vérifie si un identifiant de variable est valide (non vide) *)
(* idvar -> bool *)
let verif_id_var (id : idvar) = id <> "" 

(* Vérifie si une liste de variables est valide *)
(* a list -> bool *)
let verif_var_list var_list =match var_list with
(* on retourne faux si la liste est vide car
si il n'y a pas d'argument alors ce n'est pas une fonction *)
| [] -> true
|_::_ -> true

(* typ -> bool *)
(* Vérifie si un type de retour est valide *)
let verif_type_retour (type_retour:typ) = 
  match type_retour with
  | TInt | TBool | TUnit | TFloat -> true

(* Vérifie la compatibilité des opérations binaires et retourne leur type si valide *)
(* binary_op -> typ option *)
let  verif_bin_op op  = match op with
  | Plus | Minus | Mult | Div -> Some TInt 
  | PlusF | MinusF | MultF | DivF -> Some TFloat
  | And | Or -> Some TBool 
  | Equal | NEqual | Less | LessEq | Great | GreatEq -> Some TBool 

(* Vérifie la compatibilité des opérations unaires et retourne leur type si valide *)
(* unary_op -> typ option *)
let verif_un_op op = match op with
| Not -> Some TBool 


(* Recherche le type d'une variable dans un environnement de types *)
(* a -> (a * b) list -> b option *)
let rec  recherche_variable_in_type_env variable (type_env)  = 
  match type_env with 
    | [] -> None
    | (x,t)::y -> if x = variable then Some t else recherche_variable_in_type_env variable y

(* Vérifie si les arguments d'une fonction correspondent aux types attendus *)
(* a list -> a list -> bool *)
let rec verif_args args_fun args_env = 
  match args_fun,args_env with
  |[],[]-> true
  |x1::l1,x2::l2 -> if x1 = x2 then verif_args l1 l2 else false
  |_ -> false

(* Vérifie si une fonction existe dans l'environnement des fonctions *)
(* a -> (a * (b list * c)) list -> b option *)
let rec verif_if_fun_in_fun_env fonction fun_env = 
  match fun_env with 
  | [] -> None
  | (id, (t_list, _)) :: y -> 
      if fonction = id then Some t_list  (* Correction ici *)
      else verif_if_fun_in_fun_env fonction y
  

(* Obtient le type de retour d'une fonction si elle est définie *)
(* a -> (a * (b list * c)) list -> c option *)
let rec get_fun  f fun_env = 
  match fun_env with 
    | []-> failwith "fonction pas typé"
    | (id,(_, t))::y -> if f = id then Some t else get_fun f y

(*Que font les fonctions*)
(* vérifie qu'une expression à un type donné *)
(* on vérifie que les données de l'expression corresponde au donnes du env type *)
(*  expr -> env_typ -> env_fun-> typ option*)


(* Vérifie qu'une expression est bien typée *)
let rec verif_expr (expr:expr) (type_env:env_type) (fun_env:env_fun)=
match expr with
| Var x -> recherche_variable_in_type_env x type_env
| Int _ ->  Some TInt
| Bool _ -> Some TBool
| Float _ -> Some TFloat
| BinaryOp (op, y, z) -> 
  (match verif_bin_op op, verif_expr y (type_env) fun_env, verif_expr z type_env fun_env with
  | Some TInt, Some TInt, Some TInt -> Some TInt  (* Opérations arithmétiques *)
  | Some TFloat, Some TFloat, Some TFloat -> Some TFloat  (* Opérations sur les flottants *)
  | Some TBool, Some TInt, Some TInt -> Some TBool  (* Comparaisons : >, <, =, <> ...  Ajouté *)
  | Some TBool, Some TBool, Some TBool -> Some TBool  (* Comparaisons booléennes *)
  | Some TBool, Some TFloat, Some TFloat -> Some TBool
  | _ -> None)

| UnaryOp (op, z) ->
  (match verif_un_op op, verif_expr z type_env fun_env with
   | Some TBool, Some TBool -> Some TBool
   | _ -> None) 

  | If (x, y, z) ->
  (match verif_expr x type_env fun_env, verif_expr y type_env fun_env, verif_expr z type_env fun_env with
    | Some TBool, Some t1, Some t2 -> if t1 = t2 then  Some t1  else None
    | _ -> None)
  

| Let (idvar, typ, expr1, expr2) ->
  (match verif_expr expr1 ((idvar,typ)::type_env)  fun_env with
  | Some t when t = typ -> verif_expr expr2 ((idvar, typ)::type_env)  fun_env   
  | _ -> None)
  
(* vérifie que tout les arguments de la fonction sont du meme type que le type des arguments de la fonction *)
| App (f, args) -> 
  (match verif_if_fun_in_fun_env f fun_env with
   | None -> failwith ("Function "^f^" not found in environment")
   | Some list -> 
      let args_types = List.map (fun ex -> verif_expr ex type_env fun_env) args in
      if List.for_all Option.is_some args_types then
        let args_types_unwrapped = List.map Option.get args_types in
        if verif_args args_types_unwrapped list then 
           get_fun f fun_env 
        else None
      else failwith "erreur dans APP")
  
  | Print_int exp -> 
    (match (verif_expr exp type_env fun_env) with
      | Some TInt -> Some TInt
      | _ -> failwith "pas un type int")
  | _ -> failwith "nope"

(* vérifie que la déclaration des fonctions est correcte *)
(* fun_decl -> env_type -> env_fun -> bool *)
let verif_decl_fun (fonction: fun_decl) (type_env:env_type) (fun_env:env_fun) =
  let type_env_fonction = List.append fonction.var_list type_env in
  (verif_id_fun fonction.id)
  && (verif_var_list fonction.var_list)
  && (verif_type_retour fonction.typ_retour)
  && match (verif_expr fonction.corps type_env_fonction fun_env) with
      | None -> false
      | Some _ -> true

(* Retourne la liste des types des arguments d'une fonction *)
(* fun_decl -> typ list *)
let rec verif_type_fun (f: fun_decl) : typ list = 
    match f.var_list with 
    | [] -> []
    | (_, t) :: y -> t :: verif_type_fun { f with var_list = y }
    
(* Vérifie si la fonction "main" est présente dans l'environnement des fonctions *)
(* (idvar * a) list -> bool *)
let rec verif_main_in_env_fun env_fun = match env_fun with 
  |[]->false
  |(k,_)::y-> k = "main" || verif_main_in_env_fun y

(* Vérifie si un programme est bien typé *)
(*  'programme -> bool *)
let verif_prog (simpleML: programme) =
  let rec construire_env_fun (p: programme) (env_fun: env_fun) =
    match p with
    | [] -> env_fun
    | x :: y -> construire_env_fun y ((x.id, (verif_type_fun x, x.typ_retour)) :: env_fun)
  in
  let env_fun = construire_env_fun simpleML [] in
  let rec verifier_fonctions (p: programme) =
    match p with
    | [] -> verif_main_in_env_fun env_fun
    | x :: y -> verif_decl_fun x [] env_fun && verifier_fonctions y
  in
  verifier_fonctions simpleML


