(* Belouin Eliot & Boyenval Louis-Marie*)
open Syntax
open Verif

type tretour = 
|Type of typ
|IdV of idvar
|IdF of idfun
| OpBin of binary_op
| OpUn of unary_op
| Cond of bool*expr*expr
| Let of idvar * typ * expr * expr
| App of idfun * expr list

let  eval_bin_int_op op  = match op with
  | Plus -> (+)
  | Minus -> (-)
  | Mult -> ( * )
  | Div -> ( / ) 
  | _ -> failwith "non integer"
  
  let  eval_bin_bool_op op  = match op with 
    | And -> (&&)
    | Or -> (||)
    | _ -> failwith "Opérateur non supporté"

  let  eval_bin_comp_op op  = match op with 
  | Equal -> (=)
  | NEqual -> (!=)
  | Less -> (<)
  | LessEq -> (<=)
  | Great -> (>)
  | GreatEq -> (<=)
  | _ -> failwith ""

let match_un_op op = match op with
| Not -> (!)

let match_bin_op exp = match  exp with
| Plus|Minus|Mult|Div -> eval_bin_bool_op exp 
|Or|And->eval_bin_bool_op exp
| Equal|NEqual|Less|LessEq|Great|GreatEq-> eval_bin_comp_op exp


let eval_fun_args args f =
  match args with
  | [] -> None 
  | x :: xs -> Some (List.fold_left f x xs)

(* Fonction prenant en parametre une expression et
fourni un résultat en sortie *)
(* expr -> valeur *)
let rec eval_expr (env_val : env_val) (env_fun : env_fun) (e : expr) : valeur =
  match e with
  | Var x -> (try List.assoc x env_val with Not_found -> failwith "Variable non définie")
  | IdFun _ -> failwith "IdFun n'est pas une expression évaluable"
  | Int n -> TInt n
  | Bool b -> TBool b
  | BinaryOp (op, e1, e2) -> begin
      let v1 = eval_expr env_val env_fun e1 in
      let v2 = eval_expr env_val env_fun e2 in
      match op, v1, v2 with
      | Plus, TInt i1, TInt i2 -> TInt (i1 + i2)
      | Minus, TInt i1, TInt i2 -> TInt (i1 - i2)
      | Mult, TInt i1, TInt i2 -> TInt (i1 * i2)
      | Div, TInt i1, TInt i2 when i2 <> 0 -> TInt (i1 / i2)
      | Div, _, TInt 0 -> failwith "Division par zéro"
      | And, TBool b1, TBool b2 -> TBool (b1 && b2)
      | Or, TBool b1, TBool b2 -> TBool (b1 || b2)
      | Equal, TInt i1, TInt i2 -> TBool (i1 = i2)
      | Equal, TBool b1, TBool b2 -> TBool (b1 = b2)
      | NEqual, TInt i1, TInt i2 -> TBool (i1 <> i2)
      | NEqual, TBool b1, TBool b2 -> TBool (b1 <> b2)
      | Less, TInt i1, TInt i2 -> TBool (i1 < i2)
      | LessEq, TInt i1, TInt i2 -> TBool (i1 <= i2)
      | Great, TInt i1, TInt i2 -> TBool (i1 > i2)
      | GreatEq, TInt i1, TInt i2 -> TBool (i1 >= i2)
      | _, _, _ -> failwith "Opération sur des types incompatibles" end

  | UnaryOp (Not, e1) -> begin
      let v1 = eval_expr env_val env_fun e1 in
      match v1 with
      | TBool b -> TBool (not b)
      | _ -> failwith "Opération booléenne sur un type incompatible" end
  | If (e1, e2, e3) -> begin
      let v1 = eval_expr env_val env_fun e1 in
      match v1 with
      | TBool b when b -> eval_expr env_val env_fun e2
      | TBool _ -> eval_expr env_val env_fun e3
      | _ -> failwith "Condition d'un if-then-else non booléenne" end
  | Let (x, _, e1, e2) ->
      let v1 = eval_expr env_val env_fun e1 in
      let new_env = (x, v1) :: env_val in
      eval_expr new_env env_fun e2
  | App (_,_) ->
      (* let func = try List.assoc f env_fun with Not_found -> failwith "Fonction non définie" in
      let arg_values = List.map (fun e -> eval_expr env_val env_fun e) args in *)
      (* Pour l'instant, on suppose que la fonction est bien définie *)
      TInt 0


      type prog = fun_decl list


  let print_valeur valeur = print_string "\n" ;
    match valeur with
    |TInt x-> 
          print_int x;
          print_string "\n" 
    |TBool x -> 
          print_string (string_of_bool x);
          print_string "\n" 
(* Prend en parametre un programme et affiche
la valeur produite par l'évaluation de la fonction
main vrai si l'évaluation est correcte, faux sinon*)
(* Concretement prog est une liste de fonction
chaque fonction contient :
- un nom 
- des arguments
- un type de retour
- expression

pour chaque expression on souhaite l'évaluer et associé sa valeur à son id

on souhaite que le programme affiche le resultat du programme
*)
(* 'programme -> unit() *)


(* let eval_prog (p : prog) : valeur =
  let env_val = [] in
  let env_type = [] in
  let env_fun = List.map (fun decl -> (decl.id, (List.map (fun (x, t) -> t) decl.var_list, decl.typ_retour))) p in
  let main_decl = List.find (fun decl -> decl.id = "main") p in
  let main_body = main_decl.corps in
  eval_expr env_val  env_fun main_body *)

let eval_prog (p : prog) =
  let env_val = [] in
  let env_fun = List.map (fun decl -> (decl.id, (List.map (fun (_, t) -> t) decl.var_list, decl.typ_retour))) p in
  let main_decl = List.find (fun decl -> decl.id = "main") p in
  let main_body = main_decl.corps in
  print_valeur (eval_expr env_val  env_fun main_body)