(* Belouin Eliot & Boyenval Louis-Marie*)
open Syntax

(* Fonction prenant en paramètre une expression et fournissant un résultat en sortie *)
let rec eval_expr (e : expr) (env : (idvar * valeur) list) (env_fun : (idfun * fun_decl) list) =
  match e with
  | Var x -> (try List.assoc x env with Not_found -> failwith ("Variable non définie : " ^ x))
  | Int n -> VInt n
  | Bool b -> VBool b
  | BinaryOp (op, e1, e2) -> begin
      let v1 = eval_expr e1 env env_fun in
      let v2 = eval_expr e2 env env_fun in
      match op, v1, v2 with
      | Plus, VInt i1, VInt i2 -> VInt (i1 + i2)
      | Minus, VInt i1, VInt i2 -> VInt (i1 - i2)
      | Mult, VInt i1, VInt i2 -> VInt (i1 * i2)
      | Div, VInt i1, VInt i2 when i2 <> 0 -> VInt (i1 / i2)
      | Div, _, VInt 0 -> failwith "Division par zéro"
      | And, VBool b1, VBool b2 -> VBool (b1 && b2)
      | Or, VBool b1, VBool b2 -> VBool (b1 || b2)
      | Equal, VInt i1, VInt i2 -> VBool (i1 = i2)
      | Equal, VBool b1, VBool b2 -> VBool (b1 = b2)
      | NEqual, VInt i1, VInt i2 -> VBool (i1 <> i2)
      | NEqual, VBool b1, VBool b2 -> VBool (b1 <> b2)
      | Less, VInt i1, VInt i2 -> VBool (i1 < i2)
      | LessEq, VInt i1, VInt i2 -> VBool (i1 <= i2)
      | Great, VInt i1, VInt i2 -> VBool (i1 > i2)
      | GreatEq, VInt i1, VInt i2 -> VBool (i1 >= i2)
      | PlusF, VFloat n1, VFloat n2 -> VFloat (n1 +. n2) 
      | _, _, _ -> failwith "Opération sur des types incompatibles"
    end
  | UnaryOp (Not, e1) -> begin
      match eval_expr e1 env env_fun with
      | VBool b -> VBool (not b)
      | _ -> failwith "Opération booléenne sur un type incompatible"
    end
  | If (e1, e2, e3) -> begin
      match eval_expr e1 env env_fun with
      | VBool true -> eval_expr e2 env env_fun
      | VBool false -> eval_expr e3 env env_fun
      | _ -> failwith "Condition d'un if-then-else non booléenne"
    end
  | Let (x, _, e1, e2) ->
      let v1 = eval_expr e1 env env_fun in
      let new_env = (x, v1) :: env in
      eval_expr e2 new_env env_fun
  | App (fname, args) -> 
      (match List.assoc_opt fname env_fun with
      | Some func_decl ->
          let arg_values = List.map (fun e -> eval_expr e env env_fun) args in
          let param_names = List.map fst func_decl.var_list in
          let new_env = List.combine param_names arg_values @ env in
          eval_expr func_decl.corps new_env env_fun
      | None -> failwith ("Fonction non définie : " ^ fname))
  | Seq (_, _) -> failwith "to do"
  | _ -> failwith "to do"

let print_valeur valeur =
  match valeur with
  | VInt x -> print_int x; print_newline()
  | VBool x -> print_string (string_of_bool x); print_newline()
  | VFloat x -> print_float x; print_newline()
  | _ -> failwith "Valeur non prise en charge"

let eval_prog (p : programme) =
  let env_fun = List.map (fun f -> (f.id, f)) p in
  match List.assoc_opt "main" env_fun with
  | Some main_func -> print_valeur( eval_expr main_func.corps [] env_fun)
  | None -> failwith "Aucune fonction 'main' trouvée"
