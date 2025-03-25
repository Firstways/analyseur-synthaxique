(* Belouin Eliot & Boyenval Louis-Marie 684i*)
open Syntax

(* Récupère la valeur entière d'une expression de type VInt, sinon lève une erreur. *)
(* valeur->int *)
let get_int (exp : valeur) : int = match exp with 
  | VInt i -> i 
  | _ -> failwith "exp n'est pas de type int"

(* 
   Évalue une expression en fonction d'un environnement de variables et d'un environnement de fonctions.
   e : expr -> L'expression à évaluer.
   env : (idvar * valeur) list -> L'environnement des variables associant un identifiant à une valeur.
   env_fun : (idfun * fun_decl) list -> L'environnement des fonctions associant un identifiant à une déclaration de fonction.
*)
(* expr -> (idvar * valeur) list -> (idvar * fun_decl) list -> valeur  *)
let rec eval_expr (e : expr) (env : (idvar * valeur) list) (env_fun : (idfun * fun_decl) list) : valeur =
  match e with
  | Var x -> (try List.assoc x env with Not_found -> failwith ("Variable non définie : " ^ x))
  | Int n -> VInt n
  | Bool b -> VBool b
  | Float f -> VFloat f

  (* Évaluation des opérations binaires *)
  | BinaryOp (op, e1, e2) -> begin
      let v1 = eval_expr e1 env env_fun in
      let v2 = eval_expr e2 env env_fun in
      match op, v1, v2 with
      (* Les 4 opérations sur les entiers *)
      | Plus, VInt i1, VInt i2 -> VInt (i1 + i2)
      | Minus, VInt i1, VInt i2 -> VInt (i1 - i2)
      | Mult, VInt i1, VInt i2 -> VInt (i1 * i2)
      | Div, VInt i1, VInt i2 when i2 <> 0 -> VInt (i1 / i2)
      | Div, _, VInt 0 -> failwith "Division par zéro"

      (* Les 2 opérations logique et/ou *)
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

      | Equal, VFloat i1, VFloat i2 -> VBool (i1 = i2)
      | NEqual, VFloat i1, VFloat i2 -> VBool (i1 <> i2)
      | Less, VFloat i1, VFloat i2 -> VBool (i1 < i2)
      | LessEq, VFloat i1, VFloat i2 -> VBool (i1 <= i2)
      | Great, VFloat i1, VFloat i2 -> VBool (i1 > i2)
      | GreatEq, VFloat i1, VFloat i2 -> VBool (i1 >= i2)
      

      (* Les 4 opérations sur les flottants *)
      | PlusF, VFloat f1, VFloat f2 -> VFloat (f1 +. f2) 
      | MinusF, VFloat f1, VFloat f2 -> VFloat (f1 -. f2) 
      | MultF, VFloat f1, VFloat f2 -> VFloat (f1 *. f2) 
      | DivF, VFloat f1, VFloat f2 when f2 <> 0. -> VFloat (f1 /. f2) 
      | DivF, _, VFloat 0. -> failwith "Division par zéro"

      (* erreur pour des types n'étant pas compatible avec l'opérateur binaire *)
      | _, _, _ -> failwith "Opération sur des types incompatibles"
    end

  (* Évaluation d'opération unaire *)
  | UnaryOp (Not, e1) -> begin
      match eval_expr e1 env env_fun with
      | VBool b -> VBool (not b)
      | _ -> failwith "Opération booléenne sur un type incompatible"
    end

  (* Évaluation d'une expression conditionnelle (if-then-else) *)
  | If (e1, e2, e3) -> begin
      match eval_expr e1 env env_fun with
      | VBool true -> eval_expr e2 env env_fun
      | VBool false -> eval_expr e3 env env_fun
      | _ -> failwith "Condition d'un if-then-else non booléenne"
    end

  (* Déclaration de variable avec let *)
  | Let (x, _, e1, e2) ->
      let v1 = eval_expr e1 env env_fun in
      let new_env = (x, v1) :: env in
      eval_expr e2 new_env env_fun

  (* Application d'une fonction *)
  | App (fname, args) -> 
      (match List.assoc_opt fname env_fun with
      | Some func_decl ->
          let arg_values = List.map (fun e -> eval_expr e env env_fun) args in
          let param_names = List.map fst func_decl.var_list in
          let new_env = List.combine param_names arg_values @ env in
          eval_expr func_decl.corps new_env env_fun
      | None -> failwith ("Fonction non définie : " ^ fname))

  (* Découpage d'une expression par un ; *)
  | Seq (_, _) -> failwith "non implémenté pour l'instant"

  (* Affichage d'un entier sur la sortie *)
  | Print_int exp -> VUnit (print_int (get_int (eval_expr exp env env_fun)))

  (* Autre cas menant à une erreur*)
  | _ -> failwith "expression non défini dans env_fun ou env_val"

(* 
   Affiche une valeur sur la sortie standard.
*)
(* valeur -> unit *)
let print_valeur (valeur : valeur) : unit =
  match valeur with
  | VInt x -> print_int x; print_newline()
  | VBool x -> print_string (string_of_bool x); print_newline()
  | VFloat x -> print_float x; print_newline()
  | VUnit x -> print_string (Unit.to_string x); print_newline()

(* 
   Évalue un programme en exécutant sa fonction "main".
   programme -> unit
*)
let eval_prog (p : programme) : unit =
  let env_fun = List.map (fun f -> (f.id, f)) p in (* déclaration de env_fun *)
  match List.assoc_opt "main" env_fun with
  | Some main_func -> print_valeur( eval_expr main_func.corps [] env_fun)
  | None -> failwith "Aucune fonction 'main' trouvée"
