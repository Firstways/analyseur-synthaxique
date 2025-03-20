(* Belouin Eliot & Boyenval Louis-Marie *)
open Syntax

(* Définitions des types d'environnement *)
type env_type = (idvar * typ) list
type env_fun = (idfun * (typ list * typ)) list

(* Fonctions de vérification *)

let verif_id_fun (id : idfun) = id <> "" 

let verif_id_var (id : idvar) = id <> "" 

let verif_var_list var_list = match var_list with
  | [] -> true
  | _ :: _ -> true

let verif_type_retour type_retour = match type_retour with
  | TInt -> true
  | TBool -> true
  |TUnit -> true
  |TFloat -> true

let verif_bin_op op = match op with
  | Plus | Minus | Mult | Div -> Some TInt
  | PlusF | MinusF | MultF | DivF -> Some TFloat
  | And | Or -> Some TBool 
  | Equal | NEqual | Less | LessEq | Great | GreatEq -> Some TBool 

let verif_un_op op = match op with
  | Not -> Some TBool 

let rec recherche_variable_in_type_env variable type_env = 
  match type_env with 
    | [] -> None
    | (x, t) :: y -> if x = variable then Some t else recherche_variable_in_type_env variable y

let rec verif_args args_fun args_env = 
  match args_fun, args_env with
  | [], [] -> true
  | x1 :: l1, x2 :: l2 -> if x1 = x2 then verif_args l1 l2 else false
  | _ -> false

let rec verif_if_fun_in_fun_env fonction fun_env = 
  match fun_env with 
    | [] -> None
    | (id, (t_list, _)) :: y -> 
        if fonction = id then Some t_list
        else verif_if_fun_in_fun_env fonction y

let rec get_fun f fun_env = 
  match fun_env with 
    | [] -> failwith "fonction pas typé"
    | (id, (_, t)) :: y -> if f = id then Some t else get_fun f y

let rec verif_expr (expr : expr) (type_env : env_type) (fun_env : env_fun) = 
  print_endline ("Vérification de : " ^ string_of_expr expr);
  match expr with
  | Var x -> recherche_variable_in_type_env x type_env
  | Int _ -> Some TInt
  | Bool _ -> Some TBool
  | BinaryOp (op, y, z) -> 
      (match verif_bin_op op, verif_expr y type_env fun_env, verif_expr z type_env fun_env with
      | Some TInt, Some TInt, Some TInt -> Some TInt  (* Opérations arithmétiques *)
      | Some TBool, Some TInt, Some TInt -> Some TBool  (* Comparaisons *)
      | Some TBool, Some TBool, Some TBool -> Some TBool  (* Comparaisons booléennes *)
      | _ -> None)
  | UnaryOp (op, z) ->
      (match verif_un_op op, verif_expr z type_env fun_env with
       | Some TBool, Some TBool -> Some TBool
       | _ -> None)
  | If (x, y, z) ->
      (match verif_expr x type_env fun_env, verif_expr y type_env fun_env, verif_expr z type_env fun_env with
       | Some TBool, Some t1, Some t2 -> if t1 = t2 then Some t1 else None
       | _ -> None)
  | Let (idvar, typ, expr1, expr2) ->
      (match verif_expr expr1 ((idvar, typ) :: type_env) fun_env with
       | Some t when t = typ -> verif_expr expr2 ((idvar, typ) :: type_env) fun_env
       | _ -> None)
  | App (f, args) -> 
      (match verif_if_fun_in_fun_env f fun_env with
       | None -> failwith ("Function " ^ f ^ " not found in environment")
       | Some list -> 
           let args_types = List.map (fun ex -> verif_expr ex type_env fun_env) args in
           if List.for_all Option.is_some args_types then
             let args_types_unwrapped = List.map Option.get args_types in
             if verif_args args_types_unwrapped list then 
               get_fun f fun_env 
             else None
           else failwith "erreur dans APP")
  | _ -> failwith "nope"

let verif_decl_fun (fonction : fun_decl) (type_env : env_type) (fun_env : env_fun) =
  let type_env_fonction = List.append fonction.var_list type_env in
  (verif_id_fun fonction.id)
  && (verif_var_list fonction.var_list)
  && (verif_type_retour fonction.typ_retour)
  && match verif_expr fonction.corps type_env_fonction fun_env with
      | None -> false
      | Some _ -> true

let rec verif_type_fun (f : fun_decl) : typ list = 
  match f.var_list with 
  | [] -> []
  | (_, t) :: y -> t :: verif_type_fun { f with var_list = y }

let rec verif_main_in_env_fun env_fun = 
  match env_fun with 
  | [] -> false
  | (k, _) :: y -> k = "main" || verif_main_in_env_fun y

let verif_prog (_simpleML : programme) = true