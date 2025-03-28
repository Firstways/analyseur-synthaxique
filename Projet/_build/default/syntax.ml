(* Belouin Eliot & Boyenval Louis-Marie 684i*)

(* typ représente les types de SimpleML *)
type typ = TInt | TBool | TUnit | TFloat

(* Définition de l'arbre de syntaxe abstrait des expressions de SimpleML *)

(*on introduit deux types auxilliaires pour représenter le type des identifiants 
  de variable et les identitifiants de fonction.*)
type idvar = string
type idfun = string

(* Pour factoriser la présentation des opérateurs binaires, on utilise un type énuméré
binary_op de tous les opérateurs binaires de la syntaxe de SimpleML *)

type binary_op =
  | Plus
  | Minus
  | Mult
  | Div
  | And
  | Or
  | Equal
  | NEqual
  | Less
  | LessEq
  | Great
  | GreatEq
  | PlusF
  | MinusF
  | MultF
  | DivF

type unary_op = Not

type expr =
  | Var of idvar
  | IdFun of idfun
  | Int of int
  | Bool of bool
  | Float of float
  | BinaryOp of binary_op * expr * expr
  | UnaryOp of unary_op * expr
  | If of expr * expr * expr
  | Let of idvar * typ * expr * expr
  | App of idfun * expr list
  | Seq of expr * expr
  | Print_int of expr



(* Définition du type des déclarations de fonction de SimpleML *)

type fun_decl = {
  id: idfun;
  var_list: (idvar * typ) list;
  typ_retour: typ;
  corps: expr;
}


(* Définition du type des programmes de SimpleML *)

type programme = fun_decl list

(* Fonctions d'affichage pour la syntaxe de SimpleML *)

let string_of_type typ = match typ with 
| TInt -> "int" 
| TBool -> "bool"
| TUnit -> "unit"
| TFloat -> "float"


let string_of_binary_op binop =
  match binop with
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Div -> "/"
  | And -> "and"
  | Or -> "or"
  | Equal -> "="
  | NEqual -> "!="
  | Less -> "<"
  | LessEq -> "<="
  | Great -> ">"
  | GreatEq -> ">="
  | PlusF -> "+."
  | MinusF -> "-."
  | MultF -> "*."
  | DivF -> "/."


let string_of_unary_op unop = match unop with Not -> "not"

let rec string_of_expr_list expr_list =
  match expr_list with
  | [] -> ""
  | [ e ] -> string_of_expr e
  | e :: expr_list' -> string_of_expr e ^ "," ^ string_of_expr_list expr_list'

and string_of_expr expr =
  match expr with
  | Var x -> x
  | IdFun x -> x
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Float f -> string_of_float f  (* Gestion des flottants *)
  | BinaryOp (binop, expr1, expr2) ->
      string_of_expr expr1 ^ string_of_binary_op binop ^ string_of_expr expr2
  | UnaryOp (unop, expr) -> string_of_unary_op unop ^ string_of_expr expr
  | If (expr1, expr2, expr3) ->
      "if " ^ string_of_expr expr1 ^ " then " ^ string_of_expr expr2 ^ " else "
      ^ string_of_expr expr3
  | Let (idvar, typ, expr1, expr2) ->
      "let (" ^ idvar ^ ":" ^ string_of_type typ ^ ") = " ^ string_of_expr expr1
      ^ " in " ^ string_of_expr expr2
  | App (idfun, expr_list) -> idfun ^ "(" ^ string_of_expr_list expr_list ^ ")"
  | Seq (e1, e2) -> string_of_expr e1 ^ "; " ^ string_of_expr e2
  | Print_int (e) -> string_of_expr e
 

let rec string_of_var_list var_list =
  match var_list with
  | [] -> ""
  | [ (x, ty) ] -> x ^ ":" ^ string_of_type ty
  | (x, ty) :: var_list' ->
      x ^ ":" ^ string_of_type ty ^ "," ^ string_of_var_list var_list'

let string_of_fun_decl fdecl =
  "let " ^ fdecl.id ^ "("
  ^ string_of_var_list fdecl.var_list
  ^ ") : "
  ^ string_of_type fdecl.typ_retour
  ^ " = " ^ string_of_expr fdecl.corps

let string_of_programme prog =
  List.fold_left
    (fun str_res fdecl -> string_of_fun_decl fdecl ^ "\n" ^ str_res)
    "" prog



(* type utilisé pour vérifie le typage  *)
(* au début nous avons une liste vide
dès qu'une variable est trouvé, on l'ajoute ainsi 
que son type  *)
(* Associe un type a une variable *)
type env_type = (idvar * typ) list


type env_fun = (idfun * (typ list * typ)) list

(* type env_decl = (idfun * fun_decl) list *)


(* type env_val = (idvar * valeur) list *)
type valeur = VInt of int | VBool of bool | VUnit of unit | VFloat of float