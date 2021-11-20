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
  | List of lterme list
  | Head
  | Tail
  | Cons
  | If_empty of lterme * lterme * lterme
  | Fix of string * lterme

(* Types *)
type stype = 
  | Var of string 
  | Arr of stype * stype
  | N
  | List of stype
  | Forall of string * stype

(* Environnements de typage *) 
type env = (string * stype) list 

(* Listes d'equations *) 
type equations = (stype * stype) list

let rec print_terme (lt : lterme) : string = 
  match lt with
  | Var x -> x
  | App (t1, t2) -> "(" ^ (print_terme t1) ^ " " ^ (print_terme t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ (print_terme t) ^ ")"
  | Num n -> string_of_int n
  | Add (t1, t2) -> "(" ^ (print_terme t1) ^ " + " ^ (print_terme t2) ^ ")"
  | Sub (t1, t2) -> "(" ^ (print_terme t1) ^ " - " ^ (print_terme t2) ^ ")"
  | If_zero (t1, t2, t3) -> "(if_zero " ^ (print_terme t1) ^ " then " ^ (print_terme t2) ^ " else " ^ (print_terme t3) ^ ")"
  | Let (x, t1, t2) -> "(let " ^ x ^ " = " ^ (print_terme t1) ^ " in " ^ (print_terme t2) ^ ")"
  | List l -> "[" ^ (String.concat ", " (List.map print_terme l)) ^ "]"
  | Head -> "hd"
  | Tail -> "tl"
  | Cons -> "::"
  | If_empty (t1, t2, t3) -> "(if_empty " ^ (print_terme t1) ^ " then " ^ (print_terme t2) ^ " else " ^ (print_terme t3) ^ ")"
  | Fix (x, t) -> "(fix " ^ x ^ " -> " ^ (print_terme t) ^ ")"

let rec print_type (st : stype) : string = 
  match st with
  | Var x -> x
  | Arr (st1, st2) -> "(" ^ (print_type st1) ^ " -> " ^ (print_type st2) ^ ")"
  | N -> "N"
  | List t -> "[" ^ (print_type t) ^ "]"
  | Forall (x, t) -> "∀" ^ x ^ "." ^ (print_type t)

let rec substitue (v : string) (t_sub : stype) (t : stype) =
  match t with
  | Var v1 when v1 = v -> t_sub
  | Var v1 -> Var v1
  | Arr (t1, t2) -> Arr (substitue v t_sub t1, substitue v t_sub t2)
  | N -> N
  | List t -> List (substitue v t_sub t)
  | Forall (x, t) -> Forall (x, substitue v t_sub t)

let rec stype_equal (st1 : stype) (st2 : stype) : bool =
  match st1, st2 with
  | Var x, Var y -> x = y
  | Arr (st11, st12), Arr (st21, st22) -> (stype_equal st11 st21) && (stype_equal st12 st22)
  | N, N -> true
  | List t1, List t2 -> stype_equal t1 t2
  | Forall (x1, t1), Forall (x2, t2) ->
    let t2_sub = substitue x2 (Var x1) t2 in
    stype_equal t1 t2_sub
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
  | List t -> occur_check v t
  | Forall (x, t) -> occur_check v t

let substitue_all (v : string) (t_sub : stype) (eqs : equations) : equations = 
  List.map (fun (t1, t2) -> (substitue v t_sub t1, substitue v t_sub t2)) eqs

let rec find_type_in_equations (var : string) (eqs : equations) : stype = 
  match eqs with
  | [] -> raise VarPasTrouve
  | (Var v, t)::_ when v = var -> t
  | (t, Var v)::_ when v = var -> t
  | _::e -> find_type_in_equations var e

let rec remove_var (v : string) (l : string list) : string list = 
  match l with
  | [] -> []
  | x::lt when x = v -> remove_var v lt
  | x::lt -> x::(remove_var v lt)

let rec var_libres (t : stype) : string list = 
  match t with
  | Var v -> [v]
  | N -> []
  | Arr (t1, t2) -> 
    let vl1 = var_libres t1 in
    let vl2 = var_libres t2 in
    let vl2_red = List.filter (fun x -> not (List.mem x vl1)) vl2 in
    vl1 @ vl2_red
  | List t -> var_libres t
  | Forall (v, t) -> 
    let vl = var_libres t in
    remove_var v vl

let rec generalise_var_libres (vl : string list) (t : stype) = 
  match vl with
  | [] -> t
  | v::vlt -> generalise_var_libres vlt (Forall (v, t))

let generalise (t : stype) : stype = 
  let vl = var_libres t in
  generalise_var_libres vl t

let rec search_var_lies (v : string) (var_lies : (string * string) list) : string = 
  match var_lies with
  | [] -> v
  | (x, x_new)::vlt when x = v -> x_new
  | (x, _)::vlt -> search_var_lies v vlt

let rec barendregt_substitute (t : stype) (var_lies : (string * string) list) : stype =
  match t with
  | Var v -> Var (search_var_lies v var_lies)
  | N -> N
  | Arr (t1, t2) -> Arr (barendregt_substitute t1 var_lies, barendregt_substitute t2 var_lies)
  | List t -> List (barendregt_substitute t var_lies)
  | Forall (v, t) -> barendregt_substitute t ((v, nouvelle_var ())::var_lies)

let barendregt (t : stype) : stype = 
  barendregt_substitute t []

exception UnificationError of string
exception TypeError of string

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
  | List l ->
    let nv = nouvelle_var () in
    List.fold_left (fun x y -> x @ (gen_equas y (Var nv) e)) [(ty, List (Var nv))] l
  | Head ->
    let nv : string = nouvelle_var () in
    [(ty, Forall (nv, Arr (List (Var nv), Var nv)))]
  | Tail ->
    let nv : string = nouvelle_var () in
    [(ty, Forall (nv, Arr (List (Var nv), List (Var nv))))]
  | Cons ->
    let nv : string = nouvelle_var () in
    [(ty, Forall (nv, Arr (Var nv, Arr (List (Var nv), List (Var nv)))))]
  | If_empty (t1, t2, t3) ->
    let nv : string = nouvelle_var () in
    let eq1 : equations = gen_equas t1 (Forall (nv, List (Var nv))) e in
    let eq2 : equations = gen_equas t2 ty e in
    let eq3 : equations = gen_equas t3 ty e in
    eq1 @ eq2 @ eq3
  | Let (x, t1, t2) ->
    (try
      let ty1 : stype = typer t1 in
      let tx : stype = generalise ty1 in
      gen_equas t2 ty ((x, tx)::e)
    with TypeError e -> raise (TypeError e))
  | Fix (x, t) ->
    let tfix : stype = Var (nouvelle_var ()) in
    (ty, tfix)::(gen_equas t tfix ((x, tfix)::e))

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
      raise (UnificationError "type cible pas trouvé"))
  | e1, (Var v, t)::e2 when v == var -> unification ((Var v, t)::e1) e2 var
  | e1, (t, Var v)::e2 when v == var -> unification ((t, Var v)::e1) e2 var
  | e1, ((Forall (x, tx), t)::e2) ->
    let tbar = barendregt (Forall (x, tx)) in
    unification e1 ((tbar, t)::e2) var
  | e1, ((t, Forall (x, tx))::e2) ->
    let tbar = barendregt (Forall (x, tx)) in
    unification e1 ((t, tbar)::e2) var
  | e1, (t1, t2)::e2 when stype_equal t1 t2 -> unification e1 e2 var
  | e1, (Var v, t)::e2 | e1, (t, Var v)::e2 ->
    if occur_check v t then
      raise (UnificationError ("occurence de " ^ v ^ " dans " ^(print_type t)))
    else
      unification (substitue_all v t e1) (substitue_all v t e2) var
  | e1, (Arr (t1, t2), Arr (t3, t4))::e2 -> unification e1 ((t1, t3)::(t2, t4)::e2) var
  | e1, (List t1, List t2):: e2 -> unification e1 ((t1, t2)::e2) var
  | _, (N, t)::_ | _, (t, N)::_ ->
    raise (UnificationError ("type entier non-unifiable avec " ^ (print_type t))) 
  | _, (List tl, t)::_ | _, (t, List tl)::_ -> 
    raise (UnificationError ("type liste " ^ (print_type t) ^ " non-unifiable avec " ^ (print_type t))) 

and typer (lt : lterme) : stype = 
  let var = "T" in
  let eqs = gen_equas lt (Var var) [] in
  try
    unification [] eqs var 
  with err -> raise err

let inference (lt : lterme) : string = 
  try
    let res = typer lt in
    (print_terme lt) ^ " ***TYPABLE*** avec le type " ^ (print_type res)
  with UnificationError e | TypeError e -> (print_terme lt) ^ " ***PAS TYPABLE*** " ^ e

let ex_id : lterme = Abs("x", Var("x"))

let ex_k : lterme = Abs("x", Abs("y", Var("x")))

let ex_s : lterme = Abs("x", Abs("y", Abs("z", App(App(Var("x"), Var("z")), App(Var("y"), Var("z"))))))

let ex_omega : lterme = App (Abs ("x", App (Var "x", Var "x")), Abs ("y", App (Var "y", Var "y")))

let ex_add12 : lterme = Add (Num 1, Num 2)

let ex_add123 : lterme = Add (Num 1, Add(Num 2, Num 3))

let ex_app_id : lterme = App (Abs("x", Var("x")), Num 1)

let ex_if : lterme = If_zero (Num 0, Num 0, Num 1)

let ex_ff : lterme = Abs ("f", App (Var "f", Var "f"))

let ex_ff_id : lterme = App (ex_ff, ex_id)

let ex_let : lterme = Let ("x", Num 1, Var "x")

let ex_let1 : lterme = Let ("f", Abs("x", Var "x"), App (Var "f", Num 3))

let ex_let2 : lterme = Let ("f", Abs("x", Var "x"), App (Var "f", Abs("y", Var "y")))

let ex_let3 : lterme = Let ("f", Abs("x", Var "x"), App(App (Var "f", Abs ("y", Var "y")) , App (Var "f", Num 3)))

let ex_list : lterme = List ([Num 1; Num 2; Num 3])

let ex_hd : lterme = Head

let ex_hd_list : lterme = App (Head, ex_list)

let ex_hd_fail : lterme = App (Head, List ([Num 1; Num 2; Head]))

let ex_let_list : lterme = Let ("x", Num 3, List ([Num 1; Num 2; Var "x"]))

let ex_hd_let : lterme = App (Head, ex_let_list)

let ex_cons : lterme = App (App (Cons, Num 1), ex_list)

let ex_sum : lterme = Fix ("sum", Abs ("x", If_zero (Var "x", Num 0, Add (Var "x", App (Var "sum", Sub (Var "x", Num 1))))))

let ex_sum10 : lterme = App (ex_sum, Num 10)

let main () = 
  print_endline (inference ex_id);
  print_endline (inference ex_k);
  print_endline (inference ex_s);
  print_endline (inference ex_add12);
  print_endline (inference ex_add123);
  print_endline (inference ex_app_id);
  print_endline (inference ex_if);
  print_endline (inference ex_let);
  print_endline (inference ex_let1);
  print_endline (inference ex_let2);
  print_endline (inference ex_let3);
  print_endline (inference ex_list);
  print_endline (inference ex_hd);
  print_endline (inference ex_hd_list);
  print_endline (inference ex_hd_fail);
  print_endline (inference ex_hd_let);
  print_endline (inference ex_let_list);
  print_endline (inference ex_cons);
  print_endline (inference ex_sum);
  print_endline (inference ex_sum10);
  print_endline (inference ex_ff);
  print_endline (inference ex_ff_id);
  print_endline (inference ex_omega)

let _ = main ()
