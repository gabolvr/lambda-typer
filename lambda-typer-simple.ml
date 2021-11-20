(* Termes *)
type lterme = 
  | Var of string 
  | App of lterme * lterme
  | Abs of string * lterme

(* Types *)
type stype = 
  | Var of string 
  | Arr of stype * stype

(* Environnements de typage *) 
type env = (string * stype) list 

(* Listes d'equations *) 
type equations = (stype * stype) list

let rec print_terme (lt : lterme) : string = 
  match lt with
  | Var x -> x
  | App (lt1, lt2) -> "(" ^ (print_terme lt1) ^ " " ^ (print_terme lt2) ^ ")"
  | Abs (x, lt) -> "(fun " ^ x ^ " -> " ^ (print_terme lt) ^ ")"

let rec print_type (st : stype) : string = 
  match st with
  | Var x -> x
  | Arr (st1, st2) -> "(" ^ (print_type st1) ^ " -> " ^ (print_type st2) ^ ")"

let rec stype_equal (st1 : stype) (st2 : stype) : bool =
  match st1, st2 with
  | Var x, Var y -> x = y
  | Arr (st11, st12), Arr (st21, st22) -> (stype_equal st11 st21) && (stype_equal st12 st22)
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

let rec occur_check (v : string) (t : stype) = 
  match t with
  | Var v1 -> v1 = v
  | Arr (t1, t2) -> (occur_check v t1) || (occur_check v t2)

let rec substitue (v : string) (t_sub : stype) (t : stype) =
  match t with
  | Var v1 when v1 = v -> t_sub
  | Var v1 -> Var v1
  | Arr (t1, t2) -> Arr (substitue v t_sub t1, substitue v t_sub t2)

let substitue_all (v : string) (t_sub : stype) (eqs : equations) : equations = 
  List.map (fun (t1, t2) -> (substitue v t_sub t1, substitue v t_sub t2)) eqs

exception UnificationCycle

let rec unification (eqs_uni : equations) (eqs : equations) (var : string) : equations = 
  match eqs_uni, eqs with
  | e1, [] -> e1
  | e1, (Var v, t)::e2 when v == var -> unification ((Var v, t)::e1) e2 var
  | e1, (t1, t2)::e2 when stype_equal t1 t2 -> unification e1 e2 var
  | e1, (Var v, t)::e2 | e1, (t, Var v)::e2 ->
    if occur_check v t then
      raise UnificationCycle
    else
      unification (substitue_all v t e1) (substitue_all v t e2) var
  | e1, (Arr (t1, t2), Arr (t3, t4))::e2 -> unification e1 ((t1, t3)::(t2, t4)::e2) var
  
let rec find_type_in_equations (var : string) (eqs : equations) : stype = 
  match eqs with
  | [] -> raise VarPasTrouve
  | (Var v, t)::_ when v = var -> t
  | (t, Var v)::_ when v = var -> t
  | _::e -> find_type_in_equations var e

let inference (lt : lterme) : string = 
  let var = "T" in
  let eqs = gen_equas lt (Var var) [] in
  try
    let eqs_uni = unification [] eqs var in
    let res = find_type_in_equations var eqs_uni in
    (print_terme lt) ^ " ***TYPABLE*** avec le type " ^ (print_type res)
  with _ -> (print_terme lt) ^ " ***PAS TYPABLE***"

let ex_id : lterme = Abs("x", Var("x"))

let ex_k : lterme = Abs("x", Abs("y", Var("x")))

let ex_s : lterme = Abs("x", Abs("y", Abs("z", App(App(Var("x"), Var("z")), App(Var("y"), Var("z"))))))

let ex_omega : lterme = App (Abs ("x", App (Var "x", Var "x")), Abs ("y", App (Var "y", Var "y")))


let main () = 
  print_endline (print_terme ex_id);
  print_endline (print_terme ex_k);
  print_endline (print_terme ex_s);
  Printf.printf "%B\n" (stype_equal (Arr(Var("x"), Var("y"))) (Var("x")));
  List.iter (fun (st1, st2) -> print_endline ((print_type st1) ^ " = " ^ (print_type st2))) (gen_equas ex_id (Var "T") []);
  print_endline "======================";
  print_endline (inference ex_id);
  print_endline (inference ex_k);
  print_endline (inference ex_s);
  print_endline (inference ex_omega)

let _ = main ()
