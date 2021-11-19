(* Termes *)
type lterme = 
  | Var of string 
  | App of lterme * lterme
  | Abs of string * lterme
  | Num of int
  | Add of lterme * lterme
  | Sub of lterme * lterme
  | If_zero of lterme * lterme * lterme
  | Let of string * lterme * lterme

(* Types *)
type stype = 
  | Var of string 
  | Arr of stype * stype
  | N
  (* | List of stype
  | Forall of string * stype *)

(* Environnements de typage *) 
type env = (string * stype) list 

(* Listes d'equations *) 
type equations = (stype * stype) list

type equations_pair = equations * equations

let rec print_terme (lt : lterme) : string = 
  match lt with
  | Var x -> x
  | App (t1, t2) -> "(" ^ (print_terme t1) ^ " " ^ (print_terme t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ (print_terme t) ^ ")"
  | Num n -> string_of_int n
  | Add (t1, t2) -> "(" ^ (print_terme t1) ^ " + " ^ (print_terme t2) ^ ")"
  | Sub (t1, t2) -> "(" ^ (print_terme t1) ^ " - " ^ (print_terme t2) ^ ")"
  | If_zero (t1, t2, t3) -> "(if_zero " ^ (print_terme t1) ^ " then " ^ (print_terme t2) ^ " else " ^ (print_terme t3) ^ ")"
  | Let (x, t1, t2) -> "let " ^ x ^ " = " ^ (print_terme t1) ^ " in " ^ (print_terme t2) ^ ")"

let rec print_type (st : stype) : string = 
  match st with
  | Var x -> x
  | Arr (st1, st2) -> "(" ^ (print_type st1) ^ " -> " ^ (print_type st2) ^ ")"
  | N -> "N"
  (* | List t -> "[" ^ (print_type t) ^ "]"
  | Forall (x, t) -> "∀" ^ x ^ "." ^ (print_type t) *)

let rec stype_equal (st1 : stype) (st2 : stype) : bool =
  match st1, st2 with
  | Var x, Var y -> x = y
  | Arr (st11, st12), Arr (st21, st22) -> (stype_equal st11 st21) && (stype_equal st12 st22)
  | N, N -> true
  (* | List t1, List t2 -> stype_equal t1 t2 *)
  | _, _ -> false

(* Generateur de noms frais de variables de types *)
let compteur_var : int ref = ref 0

let nouvelle_var () : string = 
  compteur_var := !compteur_var + 1;
  "T" ^ (string_of_int !compteur_var)

exception VarPasTrouve

let rec cherche_type (v : string) (e : env) : stype = 
  match e with
  | [] -> raise VarPasTrouve
  | (v1, t1)::q when v1 = v -> t1
  | (_, _)::q -> cherche_type v q

let rec occur_check (v : string) (t : stype) = 
  match t with
  | Var v1 -> v1 = v
  | Arr (t1, t2) -> (occur_check v t1) || (occur_check v t2)
  | N -> false
  (* | List t -> occur_check v t
  | Forall (x, t) -> occur_check v t *)

let rec substitue (v : string) (t_sub : stype) (t : stype) =
  match t with
  | Var v1 when v1 = v -> t_sub
  | Var v1 -> Var v1
  | Arr (t1, t2) -> Arr (substitue v t_sub t1, substitue v t_sub t2)
  | N -> N
  (* | List t -> List (substitue v t_sub t)
  | Forall (x, t) -> Forall (x, substitue v t_sub t) *)

let substitue_all (v : string) (t_sub : stype) (eqs : equations) : equations = 
  List.map (fun (t1, t2) -> (substitue v t_sub t1, substitue v t_sub t2)) eqs

let substitue_all_pair (v : string) (t_sub : stype) ((e1, e2): equations_pair) : equations_pair = 
  (substitue_all v t_sub e1, substitue_all v t_sub e2)

exception UnificationError

let rec find_type_in_equations (var : string) (eqs : equations) : stype = 
  match eqs with
  | [] -> raise VarPasTrouve
  | (Var v, t)::_ when v = var -> t
  | (t, Var v)::_ when v = var -> t
  | _::e -> find_type_in_equations var e

let rec gen_equas (te : lterme) (ty : stype) (e : env) : equations =
  match te with
  | Var x -> 
    let tx : stype = cherche_type x e in 
    [(ty, tx)]
  | App (lt1, lt2) -> 
    let nv : string = nouvelle_var () in
    let eq1 : equations = gen_equas lt1 (Arr (Var nv, ty)) e in
    let eq2 : equations = gen_equas lt2 (Var nv) e in
    eq1 @ eq2
  | Abs (x, lt) ->
    let nv1 : string = nouvelle_var ()
    and nv2 : string = nouvelle_var () in
    (ty, (Arr (Var nv1, Var nv2)))::(gen_equas lt (Var nv2) ((x, Var nv1)::e))
  | Num _ -> [(ty, N)]
  | Add (t1, t2) | Sub (t1, t2) ->
    let eq1 : equations = gen_equas t1 N e in
    let eq2 : equations = gen_equas t2 N e in
    (ty, N)::(eq1 @ eq2)
  | If_zero (t1, t2, t3) ->
    let eq1 : equations = gen_equas t1 N e in
    let eq2 : equations = gen_equas t2 ty e in
    let eq3 : equations = gen_equas t3 ty e in
    eq1 @ eq2 @ eq3
  | Let (x, t1, t2) ->
    let ty1 : stype = unification [] (gen_equas t1 (Var "T_aux") e) "T_aux" in
    gen_equas t2 ty ((x, ty1)::e)

and unification (eqs_uni : equations) (eqs : equations) (var : string) : stype = 
  (* print_endline "eqs_uni";
  List.iter (fun (st1, st2) -> print_endline ((print_type st1) ^ " = " ^ (print_type st2))) eqs_uni;
  print_endline "eqs";
  List.iter (fun (st1, st2) -> print_endline ((print_type st1) ^ " = " ^ (print_type st2))) eqs; *)
  match (eqs_uni, eqs) with
  | e1, [] -> 
    (try
      find_type_in_equations var e1
    with VarPasTrouve ->
      raise UnificationError)
  | e1, (Var v, t)::e2 when v == var -> unification ((Var v, t)::e1) e2 var
  | e1, (t1, t2)::e2 when stype_equal t1 t2 -> unification e1 e2 var
  | e1, (Var v, t)::e2 | e1, (t, Var v)::e2 ->
    if occur_check v t then
      raise UnificationError
    else
      unification (substitue_all v t e1) (substitue_all v t e2) var
  | e1, (Arr (t1, t2), Arr (t3, t4))::e2 -> unification e1 ((t1, t3)::(t2, t4)::e2) var
  | _, (N, _)::_ -> raise UnificationError
  | _, (_, N)::_ -> raise UnificationError

let inference (lt : lterme) : string = 
  let var = "T" in
  let eqs = gen_equas lt (Var var) [] in
  try
    let res = unification [] eqs var in
    (print_terme lt) ^ " ***TYPABLE*** avec le type " ^ (print_type res)
  with _ -> (print_terme lt) ^ " ***PAS TYPABLE***"

let ex_id : lterme = Abs("x", Var("x"))

let ex_k : lterme = Abs("x", Abs("y", Var("x")))

let ex_s : lterme = Abs("x", Abs("y", Abs("z", App(App(Var("x"), Var("z")), App(Var("y"), Var("z"))))))

let ex_omega : lterme = App (Abs ("x", App (Var "x", Var "x")), Abs ("y", App (Var "y", Var "y")))

let ex_add12 : lterme = Add (Num 1, Num 2)

let ex_add123 : lterme = Add (Num 1, Add(Num 2, Num 3))

let ex_app_id : lterme = App (Abs("x", Var("x")), Num 1)

let ex_if : lterme = If_zero (Num 0, Num 0, Num 1)

let main () = 
  print_endline (inference ex_id);
  print_endline (inference ex_k);
  print_endline (inference ex_s);
  print_endline (inference ex_add12);
  print_endline (inference ex_add123);
  print_endline (inference ex_app_id);
  print_endline (inference ex_if);
  print_endline (inference ex_omega)

let _ = main ()
