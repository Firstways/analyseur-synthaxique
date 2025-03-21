(* Belouin Eliot & Boyenval Louis-Marie*)
open Syntax
open Verif


let eval_fun_args args f =
  match args with
  | [] -> None 
  | x :: xs -> Some (List.fold_left f x xs)

(* Fonction prenant en parametre une expression et
fourni un résultat en sortie *)
(* expr -> valeur *)
let rec eval_expr (env_val : env_val) (env_fun : env_fun) (e : expr) : valeur =
  match e with
  | Var x -> (try List.assoc x env with Not_found -> failwith ("Variable non définie : " ^ x))
  | Int n -> VInt n
  | Bool b -> VBool b
  | BinaryOp (op, e1, e2) -> begin
      let v1 = eval_expr e1 env env_fun in
      let v2 = eval_expr e2 env env_fun in
      match op, v1, v2 with

      | Plus, TInt i1, TInt i2 -> TInt (i1 + i2)
      | Minus, TInt i1, TInt i2 -> TInt (i1 - i2)
      | Mult, TInt i1, TInt i2 -> TInt (i1 * i2)
      | Div, TInt i1, TInt i2 when i2 <> 0 -> TInt (i1 / i2)
      | Div, _, TInt 0 -> failwith "Division par zéro"

      | PlusF, TFloat i1, TFloat i2 -> TFloat (i1 +. i2)
      | MinusF, TFloat i1, TFloat i2 -> TFloat (i1 -. i2)
      | MultF, TFloat i1, TFloat i2 -> TFloat (i1 *. i2)
      | DivF, TFloat i1, TFloat i2 -> TFloat (i1 /. i2)
      | DivF, _, TFloat 0. -> failwith "Division par zéro"

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
