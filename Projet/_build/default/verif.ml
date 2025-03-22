(* Belouin Eliot & Boyenval Louis-Marie *)
open Syntax

(* Vérifie si un identifiant de fonction est valide (différent de "") *)
(* idvar -> bool *)
let verif_id_fun (id : idfun) = id <> "" 

(* Vérifie si un identifiant de variable est valide (différent de "") *)
(* idvar -> bool *)
let verif_id_var (id : idvar) = id <> "" 

(* Vérifie si un type de retour est valide (TInt, TBool, TUnit, TFloat) *)
(* typ -> bool *)
let verif_type_retour (type_retour:typ) = match type_retour with
| TInt | TBool | TUnit | TFloat -> true

(* Vérifie si une opération binaire est valide et retourne son type *)
(* binary_op -> typ option *)
let verif_bin_op op = match op with
  | Plus | Minus | Mult | Div -> Some TInt  (* Opérations sur les entiers *)
  | PlusF | MinusF | MultF | DivF -> Some TFloat (* Opérations sur les flottants *)
  | And | Or -> Some TBool  (* Opérations booléennes *)
  | Equal | NEqual | Less | LessEq | Great | GreatEq -> Some TBool (* Comparaisons *)

(* Vérifie si une opération unaire est valide et retourne son type *)
(* unary_op -> typ option *)
let verif_un_op op = match op with
  | Not -> Some TBool (* Opération de négation booléenne *)

(* Recherche une variable dans l'environnement de types et retourne son type si trouvé *)
(* idvar -> (idvar * typ) list -> typ option *)
let rec recherche_variable_in_type_env variable type_env = 
  match type_env with 
    | [] -> None
    | (x, t)::y -> if x = variable then Some t else recherche_variable_in_type_env variable y

(* Vérifie que les arguments passés à une fonction correspondent à son type attendu *)
(* typ list -> typ list -> bool *)
let rec verif_args args_fun args_env = 
  match args_fun, args_env with
  | [], [] -> true
  | x1::l1, x2::l2 -> if x1 = x2 then verif_args l1 l2 else false
  | _ -> false (* Les listes ont une longueur différente *)

(* Recherche une fonction dans l'environnement des fonctions et retourne ses types d'arguments *)
(* idfun -> (idfun * (typ list * typ)) list -> typ list option *)
let rec verif_if_fun_in_fun_env fonction fun_env = 
  match fun_env with 
  | [] -> None
  | (id, (t_list, _)) :: y -> 
      if fonction = id then Some t_list  
      else verif_if_fun_in_fun_env fonction y

(* Récupère le type de retour d'une fonction *)
(* idfun -> (idfun * (typ list * typ)) list -> typ option *)
let rec get_fun f fun_env = 
  match fun_env with 
    | [] -> failwith "Fonction non typée"
    | (id, (_, t))::y -> if f = id then Some t else get_fun f y

(* Vérifie le typage d'une expression *)
(* expr -> env_type -> env_fun -> typ option *)
let rec verif_expr (expr:expr) (type_env:env_type) (fun_env:env_fun) = 
  (* print_endline ("Vérification de : " ^ string_of_expr expr); *)
  match expr with
  | Var x -> recherche_variable_in_type_env x type_env (* Recherche le type de la variable *)
  | Int _ -> Some TInt
  | Bool _ -> Some TBool
  | BinaryOp (op, y, z) -> 
    (* Vérifie que les opérandes et l'opération sont compatibles *)
    (match verif_bin_op op, verif_expr y type_env fun_env, verif_expr z type_env fun_env with
    | Some TInt, Some TInt, Some TInt -> Some TInt  
    | Some TBool, Some TInt, Some TInt -> Some TBool  
    | Some TBool, Some TBool, Some TBool -> Some TBool  
    | _ -> None)
  | UnaryOp (op, z) ->
    (match verif_un_op op, verif_expr z type_env fun_env with
     | Some TBool, Some TBool -> Some TBool
     | _ -> None)
  | If (x, y, z) ->
    (* Vérifie que la condition est un booléen et que les deux branches ont le même type *)
    (match verif_expr x type_env fun_env, verif_expr y type_env fun_env, verif_expr z type_env fun_env with
      | Some TBool, Some t1, Some t2 -> if t1 = t2 then Some t1 else None
      | _ -> None)
  | Let (idvar, typ, expr1, expr2) ->
    (* Vérifie que l'expression correspond au type déclaré et continue avec le nouvel environnement *)
    (match verif_expr expr1 ((idvar, typ)::type_env) fun_env with
    | Some t when t = typ -> verif_expr expr2 ((idvar, typ)::type_env) fun_env   
    | _ -> None)
  | App (f, args) -> 
    (* Vérifie l'application d'une fonction *)
    (match verif_if_fun_in_fun_env f fun_env with
     | None -> failwith ("Function "^f^" not found in environment")
     | Some list -> 
         let args_types = List.map (fun ex -> verif_expr ex type_env fun_env) args in
         if List.for_all Option.is_some args_types then
           let args_types_unwrapped = List.map Option.get args_types in
           if verif_args args_types_unwrapped list then 
             get_fun f fun_env 
           else None
         else failwith "Erreur dans App")
  | _ -> failwith "Expression non supportée"

(* Vérifie la déclaration d'une fonction en testant son id, son type de retour et le typage de son corps *)
(* fun_decl -> env_type -> env_fun -> bool *)
let verif_decl_fun (fonction: fun_decl) (type_env:env_type) (fun_env:env_fun) =
  let type_env_fonction = List.append fonction.var_list type_env in
  (verif_id_fun fonction.id)
  && (verif_type_retour fonction.typ_retour)
  && match (verif_expr fonction.corps type_env_fonction fun_env) with
      | None -> false
      | Some _ -> true

(* Retourne la liste des types des paramètres d'une fonction *)
(* fun_decl -> typ list *)
let rec verif_type_fun (f: fun_decl) : typ list = 
  match f.var_list with 
  | [] -> []
  | (_, t) :: y -> t :: verif_type_fun { f with var_list = y }

(* Vérifie si la fonction "main" est présente dans l'environnement des fonctions *)
(* (idvar * a) list -> bool *)
let rec verif_main_in_env_fun env_fun = 
  match env_fun with 
  | [] -> false
  | (k, _) :: y -> k = "main" || verif_main_in_env_fun y

(* Vérifie le typage global d'un programme *)
(* programme -> bool *)
let verif_prog (simpleML: programme) =
  (* Construit l'environnement des fonctions à partir du programme *)
  let rec construire_env_fun (p: programme) (env_fun: env_fun) =
    match p with
    | [] -> env_fun
    | x :: y -> construire_env_fun y ((x.id, (verif_type_fun x, x.typ_retour)) :: env_fun)
  in
  let env_fun = construire_env_fun simpleML [] in
  (* Vérifie le typage de chaque fonction et s'assure que "main" est bien défini *)
  let rec verifier_fonctions (p: programme) =
    match p with
    | [] -> verif_main_in_env_fun env_fun
    | x :: y -> verif_decl_fun x [] env_fun && verifier_fonctions y
  in
  verifier_fonctions simpleML
