(** 
  Un interpréteur pour un langage imperatif et un prouveur en logique de Hoare 
  et un prouveur en logique de Hoare.
  @author Frejoux Gaetan, Niord Mathieu & Sauzeau Yannis
*)

(**
Print result and check assertion.
@param wanted : The wanted string
@param exp : The exp_to_string
*)
let print_result (result : string) (wanted : string) : unit =
  Printf.printf "\nObtenu :\n%s\nAttendu :\n%s\n" result wanted;
  assert (String.equal result wanted);
;;

(**
Print question header and results through a list.
@param exercise : Exercise number [int]
@param section  : Section number [int]
@param question : Question number [int]
@param results  : List of pairs as (result, wanted [string]) [('a * string) list]
@param str_convertor : String's conversion functor [<fun>]
*)
let print_header_results (exercise : int) (section : int) (question : int) (results : ('a * string) list) (str_convertor) : unit =
  Printf.printf ("\n=== EXERCICE %d, Partie %d : Question %d ===\n\n") exercise section question;
  List.iter (fun (res, wanted) -> print_result (str_convertor res) (wanted)) results;
  Printf.printf ("\n")
;;

(* 1. Un interpreteur pour un langage imperatif *)
(* 1.1 Les expressions arithmetiques *)
(* 1.1.1 Syntaxe abstraite*)

(* Question 1. *)

(** Type énuméré [operator] : Addition, Soustraction et Multiplication. *)
type operator = ADD | MINUS | MULT;;
(** Type [aexp] : Donne la syntaxe abstraite des expressions arithmétiques. *)
type aexp = 
  | Const of int 
  | Var of string 
  | Ope of aexp * aexp * operator;;

(* Question 2. *)

(* (2) *)
let aexp_01 = Const(2);;

(* (2 + 3) *)
let aexp_02 = Ope(Const(2), Const(3), ADD);;

(* (2 - 5) *)
let aexp_03 = Ope(Const(2), Const(5), MINUS);;

(* (3 * 6) *)
let aexp_04 = Ope(Const(3), Const(6), MULT);;

(* (2 + x) *)
let aexp_05 = Ope(Const(2), Var("x"), ADD);;

(* (4 * y) *)
let aexp_06 = Ope(Const(4), Var("y"), MULT);;

(* (3 * x * x) *)
let aexp_07 = Ope(
    Ope(Const(3), Var("x"), MULT),
    Var("x"),
    MULT
  )
;;

(* (5 * x + 7 * y) *)
let aexp_08 = Ope(
    Ope(Const(5), Var("x"), MULT),
    Ope(Const(7), Var("y"), MULT),
    ADD
  )
;;

(* (6 * x + 5 * y * x) *)
let aexp_09 = Ope(
    Ope(Const(6), Var("x"), MULT),
    Ope(Const(5),Ope( Var("y"), Var("x"), MULT), MULT),
    ADD
  )
;;


(* Question 3. *)

(* 3.1 *)
let operator_to_string (o : operator) : string =
  match o with
  | ADD  -> " + "
  | MINUS -> " - "
  | MULT  -> " * "
;;

let rec aexp_to_string (exp : aexp) : string = 
  match exp with
  | Const(elem) -> string_of_int elem
  | Var(elem) -> elem
  | Ope(l, r, o) -> 
      "(" ^ (aexp_to_string l) ^ (operator_to_string o) ^ (aexp_to_string r) ^ ")"
;;

(* 3.2 *)
print_header_results 1 1 3 [
  (aexp_01, "2");
  (aexp_02, "(2 + 3)");
  (aexp_03, "(2 - 5)");
  (aexp_04, "(3 * 6)");
  (aexp_05, "(2 + x)");
  (aexp_06, "(4 * y)");
  (aexp_07, "((3 * x) * x)");
  (aexp_08, "((5 * x) + (7 * y))");
  (aexp_09, "((6 * x) + (5 * (y * x)))");
] (aexp_to_string)
;;


(** 1.1.2 Interprétation *)

(** Question 4. *)

type valuation = (string * int) list;;

(** Question 5. *)

let compute (e : aexp) : int =
  match e with
  | Const(elem) -> elem
  | Ope(Const(l), Const(r), o) ->
      (
        match o with
        | ADD -> l + r
        | MINUS -> l - r
        | MULT -> l * r
      )
  | _ -> failwith "Error [compute aexp] : Cannot compute this expression !"
;;

let var_to_const (var : string) (v : valuation) : int =
  let _, value = List.find (fun (x, _) -> String.equal var x) v in
  value
;;

let rec ainterp (e : aexp) (v : valuation) : int =
  match e with
  | Const(elem) -> elem
  | Var(elem) -> (var_to_const elem v)
  | Ope(l, r, o) -> 
      let l_i : aexp = Const(ainterp l v)
      and r_i : aexp = Const(ainterp r v) in
      compute(Ope(l_i, r_i, o))
;;

(** Question 6. *)

let aexp_valuation : valuation = [("x", 5); ("y", 9)];;

print_header_results 1 1 6 [
  ((ainterp aexp_01 aexp_valuation), "2");
  ((ainterp aexp_02 aexp_valuation), "5");
  ((ainterp aexp_03 aexp_valuation), "-3");
  ((ainterp aexp_04 aexp_valuation), "18");
  ((ainterp aexp_05 aexp_valuation), "7");
  ((ainterp aexp_06 aexp_valuation), "36");
  ((ainterp aexp_07 aexp_valuation), "75");
  ((ainterp aexp_08 aexp_valuation), "88");
  ((ainterp aexp_09 aexp_valuation), "255");
] (Int.to_string)
;;


(** 1.1.3 Substitutions *)

(** Question 7. *)

let rec asubst (var : string) (subst : aexp) (e : aexp) : aexp =
  match e with
  | Var(elem) -> if (String.equal var elem) then subst else e
  | Ope(l, r, o) -> Ope((asubst var subst l), (asubst var subst r), o)
  | _ -> e
;;

let asubst_list (subs : (string * aexp) list) (e : aexp) : aexp =
  let res : aexp ref = ref e in
  List.iter (fun (s, e) -> res := (asubst s e !res)) subs;
  !res
;;

(** Question 8. *)

let x_subst : aexp = Const(7);;
let y_subst : aexp = Ope(Var("z"), Const(2), ADD);;

let subs = asubst_list ([("x", x_subst); ("y", y_subst)]);;

print_header_results 1 1 8 [
  ((subs aexp_01), "2");
  ((subs aexp_02), "(2 + 3)");
  ((subs aexp_03), "(2 - 5)");
  ((subs aexp_04), "(3 * 6)");
  ((subs aexp_05), "(2 + 7)");
  ((subs aexp_06), "(4 * (z + 2))");
  ((subs aexp_07), "((3 * 7) * 7)");
  ((subs aexp_08), "((5 * 7) + (7 * (z + 2)))");
  ((subs aexp_09), "((6 * 7) + (5 * ((z + 2) * 7)))");
] (aexp_to_string)
;;


(** 1. Les expressions booléennes *)

(** 1.2.1 Syntaxe abstraite *)

(** Question 1. *)

type bexp = 
  | True | False 
  | Not of bexp 
  | And of bexp * bexp | Or of bexp * bexp 
  | Equal of aexp * aexp
  | Le of aexp * aexp (* "Le" signifie "less or equal than to". *)
;;

(** Question 2. *)

(* (vrai) *)
let bexp_01 : bexp = True;;

(* (vrai et faux) *)
let bexp_02 : bexp = And(True, False);;

(* (non vrai) *)
let bexp_03 : bexp = Not(True);;

(* (vrai ou faux) *)
let bexp_04 : bexp = Or(True, False);;

(* (2 = 4) *)
let bexp_05 : bexp = Equal(Const(2), Const(4));;

(* (3 + 5 = 2 * 4) *)
let bexp_06 : bexp = Equal(
    Ope(Const(3), Const(5), ADD), 
    Ope(Const(2), Const(4), MULT));;

(* (2 * x = y + 1) *)
let bexp_07 : bexp = Equal(
    Ope(Const(2), Var("x"), MULT), 
    Ope(Var("y"), Const(1), ADD));;

(* (5 <= 7) *)
let bexp_08 : bexp = Le(Const(5), Const(7));;

(* (8 + 9 <= 4 * 5) et (3 + x <= 4 * y) *)
let bexp_09 : bexp = And(
    Le(Ope(Const(8), Const(9), ADD), Ope(Const(4), Const(5), MULT)),
    Le(Ope(Const(3), Var("x"), ADD), Ope(Const(4), Var("y"), MULT))
  );;

(** Question 3. *)

(* 3.1 *)
let rec bexp_to_string (b : bexp) : string =
  match b with
  | True -> "vrai"
  | False -> "faux"
  | Not(elem) -> "non (" ^ bexp_to_string elem ^ ")"
  | And(l, r) -> "(" ^ (bexp_to_string l) ^ " et " ^ (bexp_to_string r) ^ ")"
  | Or(l, r) -> "(" ^ (bexp_to_string l) ^ " ou " ^ (bexp_to_string r) ^ ")"
  | Equal(l, r) -> "(" ^ (aexp_to_string l) ^ " = " ^ (aexp_to_string r) ^ ")"
  | Le(l, r) -> "(" ^ (aexp_to_string l) ^ " <= " ^ (aexp_to_string r) ^ ")"
;;

(* 3.2 *)
print_header_results 1 2 3 [
  (bexp_01, "vrai");
  (bexp_02, "(vrai et faux)");
  (bexp_03, "non (vrai)");
  (bexp_04, "(vrai ou faux)");
  (bexp_05, "(2 = 4)");
  (bexp_06, "((3 + 5) = (2 * 4))");
  (bexp_07, "((2 * x) = (y + 1))");
  (bexp_08, "(5 <= 7)");
  (bexp_09, "(((8 + 9) <= (4 * 5)) et ((3 + x) <= (4 * y)))");
] (bexp_to_string)
;;


(** 1.2.2 Interprétation *)

(** Question 4. *)

let rec binterp (b : bexp) (v : valuation) : bool =
  match b with
  | True -> true
  | False -> false
  | Not(elem) -> not (binterp elem v)
  | And(l, r) -> (binterp l v) && (binterp r v)
  | Or(l, r) -> (binterp l v) || (binterp r v)
  | Equal(l, r) -> (ainterp l v) = (ainterp r v)
  | Le(l,r) -> (ainterp l v) <= (ainterp r v)
;;

(** Question 5. *)
let bexp_valuation : valuation = [("x", 7); ("y", 3)];;

print_header_results 1 2 5 [
  ((binterp bexp_01 bexp_valuation), "true");
  ((binterp bexp_02 bexp_valuation), "false");
  ((binterp bexp_03 bexp_valuation), "false");
  ((binterp bexp_04 bexp_valuation), "true");
  ((binterp bexp_05 bexp_valuation), "false");
  ((binterp bexp_06 bexp_valuation), "true");
  ((binterp bexp_07 bexp_valuation), "false");
  ((binterp bexp_08 bexp_valuation), "true");
  ((binterp bexp_09 bexp_valuation), "true");
] (Bool.to_string)
;;


(** 1.3 Les commandes du langage *)

(** 1.3.1 Syntaxe abstraite *)
(** Question 1. *)

type prog = 
  | Skip
  | Aff of string * aexp
  | Seq of prog * prog
  | Cond of bexp * prog * prog
  | Loop of aexp * prog
;;

(** Question 2. *)

(* (y := 7) *)
let prog_01 = Aff("y", Const(7));;

(* (z := 3 + 4 ; x := 2 * x) *)
let prog_02 = Seq
    (
      Aff("z", Ope(Const(3), Const(4), ADD)),
      Aff("x", Ope(Const(2), Var("x"), MULT))
    )
;;

(* (n := 3; if (n <= 4) then n:= 2 * n + 3 else n := n + 1) *)
let prog_03 = Seq
    (
      Aff("n", Const(3)),
      Cond
        (
          Le(Var("n"), Const(4)), 
          Aff("n", Ope(Ope(Const(2), Var("n"), MULT), Const(3), ADD)), 
          Aff("n", Ope(Var("n"), Const(1), ADD))
        )
    )
;;

(* (repeat 10 do x := x+1 od) *)
let prog_04 = Loop
    (
      Const(10), 
      Aff("x", Ope(Var("x"), Const(1), ADD))
    )
;;

(** Question 3. *)

let rec prog_to_string (program: prog) : string =
  match program with
  | Skip -> ""
  | Aff(v, e) -> v ^ " := " ^ (aexp_to_string e)
  | Seq(p1, p2) -> (prog_to_string p1) ^ ";\n" ^ (prog_to_string p2)
  | Cond(b, p1, p2) -> "if (" ^ (bexp_to_string b) ^ ")\nthen " ^ (prog_to_string p1) ^ "\nelse " ^ (prog_to_string p2)
  | Loop(e, p) -> "repeat " ^ (aexp_to_string e) ^ " do\n" ^ (prog_to_string p) ^ "\nod"
;;

print_header_results 1 3 3 [
  (prog_01, "y := 7");
  (prog_02, "z := (3 + 4);\nx := (2 * x)");
  (prog_03, "n := 3;\nif ((n <= 4))\nthen n := ((2 * n) + 3)\nelse n := (n + 1)");
  (prog_04, "repeat 10 do\nx := (x + 1)\nod");
] (prog_to_string)
;;

(** 1.3.2 Interprétation *)

(** Question 4. *)

let rec selfcompose (f : 'a -> 'a) (n : int) : 'a -> 'a = 
  if (n <= 0)
  then (fun x -> x)
  else (fun x -> (selfcompose f (n - 1)) (f x))
;;

(** Question 5. *)

Printf.printf "10 fois => f: x -> x + 2: %d\n\n" ((selfcompose (fun x -> x + 2) 10) (0));;

(** Question 6. *)

let rec exec (p : prog) (v : valuation) : valuation =
  match p with
  | Skip -> v
  | Aff(v1, e) -> (v1, (ainterp e v))::v
  | Seq(p1, p2) -> exec p2 (exec p1 v)
  | Cond(b, p1, p2) -> if (binterp b v) then (exec p1 v) else (exec p2 v)
  | Loop(e, p1) -> (selfcompose (fun nv -> exec p1 nv) (ainterp e v)) (v)
;;

(** Question 7. *)

let prog_fact : prog = 
  Seq
    ( 
      Aff("i", Const(1)),
      Loop(
        Var("in"), 
        Seq
          (
            Aff("out", Ope(Var("out"), Var("i"), MULT)),
            Seq(
              Aff("i", Ope(Var("i"), Const(1), ADD)),
              Aff("in", Ope(Var("in"), Const(1), MINUS))
            )
          )
      )
    )
;;

let fact (n : int) : int =
  let v : valuation = exec prog_fact [("in", n); ("out", 1)] in
  var_to_const ("out") v
;;

Printf.printf "Factorielle de 5 = %d\n\n" (fact 5);;

let prog_fibo : prog =
  Seq
    ( 
      Aff("b", Const(1)),
      Seq (
        Aff("t", Const(0)),
        Loop(
          Var("in"), 
          Seq
            (
              Aff("t", Var("out")),
              Seq
                (
                  Aff("out", Var("b")),
                  Seq(
                    Aff("b", Ope(Var("t"), Var("b"), ADD)),
                    Aff("in", Ope(Var("in"), Const(1), MINUS))
                  )
                )
            )
        ) 
      )
    )
;;

let fibo (n : int) : int =
  if n <= 0 then 0
  else if n = 1 then 1
  else
    let v : valuation = exec prog_fibo [("in", n); ("out", 0)] in
    var_to_const ("out") v
;;

Printf.printf "8ème nombre de la suite de Fibonacci = %d\n\n" (fibo 8);;

(** 1.4 Triplets de Hoare et validité *)

(** 1.4.1 Syntaxe abstraite des formules de la logiques des propositions *)

(** Question 1. *)

type t_prop = 
  | True | False 
  | Not of t_prop 
  | And of t_prop * t_prop | Or of t_prop * t_prop 
  | Equal of aexp * aexp
  | Le of aexp * aexp
  | Impl of t_prop * t_prop
;;

(** Question 2. *)

(* (vrai) *)
let prop_01 : t_prop = True;;

(* (vrai et faux) *)
let prop_02 : t_prop = And(True, False);;

(* (non vrai) *)
let prop_03 : t_prop = Not(True);;

(* (vrai ou faux) *)
let prop_04 : t_prop = Or(True, False);;

(* (faux implique ) *)
let prop_05 : t_prop = Impl(False, Or(True, False));;

(* (2 = 4) *)
let prop_06 : t_prop = Equal(Const(2), Const(4));;

(* (3 + 5 = 2 * 4) *)
let prop_07 : t_prop = Equal(Ope(Const(3), Const(5), ADD), Ope(Const(2), Const(4), MULT));;

(* (2 * x = y + 1) *)
let prop_08 : t_prop = Equal(Ope(Const(2), Var("x"), MULT), Ope(Var("y") , Const(1), ADD));;

(* (3 + x <= 4 * y) *)
let prop_09 : t_prop = Le(Ope(Const(3), Var("x"), ADD), Ope(Const(4) , Var("y"), MULT));;

(* (5 <= 7) et (8 + 9 <= 4 * 5) *)
let prop_10 : t_prop = And(
    Le(Const(5), Const(7)),
    Le(Ope(Const(8), Const(9), ADD), Ope(Const(4), Const(5), MULT)
      ));;

(* (x = 1) implique (y <= 0) *)
let prop_11 : t_prop = Impl(
    Equal(Var("x"), Const(1)),
    Le(Var("y"), Const(0))
  );;

(** Question 3. *)

let rec prop_to_string (prop : t_prop) : string =
  match prop with
  | True -> "vrai"
  | False -> "faux"
  | Not(elem) -> "non (" ^ prop_to_string elem ^ ")"
  | And(l, r) -> "(" ^ (prop_to_string l) ^ " et " ^ (prop_to_string r) ^ ")"
  | Or(l, r) -> "(" ^ (prop_to_string l) ^ " ou " ^ (prop_to_string r) ^ ")"
  | Equal(l, r) -> "(" ^ (aexp_to_string l) ^ " = " ^ (aexp_to_string r) ^ ")"
  | Le(l, r) -> "(" ^ (aexp_to_string l) ^ " <= " ^ (aexp_to_string r) ^ ")"
  | Impl(l, r) ->  "(" ^ (prop_to_string l) ^ " implique " ^ (prop_to_string r) ^ ")"
;;


print_header_results 1 4 1 ([
    (prop_01, "vrai");
    (prop_02, "(vrai et faux)");
    (prop_03, "non (vrai)");
    (prop_04, "(vrai ou faux)");
    (prop_05, "(faux implique (vrai ou faux))");
    (prop_06, "(2 = 4)");
    (prop_07, "((3 + 5) = (2 * 4))");
    (prop_08, "((2 * x) = (y + 1))");
    (prop_09, "((3 + x) <= (4 * y))");
    (prop_10, "((5 <= 7) et ((8 + 9) <= (4 * 5)))");
    (prop_11, "((x = 1) implique (y <= 0))");
  ]) (prop_to_string)
;;

(** 1.4.2 Interprétation *)

(** Question 4. *)
let rec pinterp (prop : t_prop) (v : valuation) : bool =
  match prop with
  | True -> true
  | False -> false
  | Not(elem) -> not (pinterp elem v)
  | And(p, q) -> (pinterp p v) && (pinterp q v)
  | Or(p, q) -> (pinterp p v) || (pinterp q v)
  | Equal(a1, a2) -> (ainterp a1 v) = (ainterp a2 v)
  | Le(a1, a2) -> (ainterp a1 v) <= (ainterp a2 v)
  | Impl(p, q) -> (not (pinterp p v)) || (pinterp q v)
;;

(** Question 5. *)
let t_prop_valuation : valuation = [("x", 7); ("y", 3)];;

print_header_results 1 4 5 [
  ((pinterp prop_01 t_prop_valuation), "true");
  ((pinterp prop_02 t_prop_valuation), "false");
  ((pinterp prop_03 t_prop_valuation), "false");
  ((pinterp prop_04 t_prop_valuation), "true");
  ((pinterp prop_05 t_prop_valuation), "true");
  ((pinterp prop_06 t_prop_valuation), "false");
  ((pinterp prop_07 t_prop_valuation), "true");
  ((pinterp prop_08 t_prop_valuation), "false");
  ((pinterp prop_09 t_prop_valuation), "true");
  ((pinterp prop_10 t_prop_valuation), "true");
  ((pinterp prop_11 t_prop_valuation), "true");
] (Bool.to_string)
;;

(** 1.4.3 Substitutions *)

(** Question 6. *)
let rec psubst (var : string) (subst : aexp) (p : t_prop) : t_prop =
  match p with
  | Not(p1) -> Not(psubst var subst p1)
  | And(p1, p2) -> And((psubst var subst p1), (psubst var subst p2))
  | Or(p1, p2) -> Or((psubst var subst p1), (psubst var subst p2))
  | Equal(a1, a2) -> Equal((asubst var subst a1), (asubst var subst a2))
  | Le(a1, a2) -> Le((asubst var subst a1), (asubst var subst a2))
  | Impl(p1, p2) -> Impl((psubst var subst p1), (psubst var subst p2))
  | _ -> p
;;

let psubst_list (subs : (string * aexp) list) (p : t_prop) : t_prop =
  let res : t_prop ref = ref p in
  List.iter (fun (s, e) -> res := (psubst s e !res)) subs;
  !res
;;

(* Question 7. *)

let x_subst : aexp = Ope(Const(3), Var("y"), MULT);;
let y_subst : aexp = Ope(Var("k"), Const(2), ADD);;

let subs = psubst_list ([("x", x_subst); ("y", y_subst)]);;

print_header_results 1 4 7 [
  ((subs prop_01), "vrai");
  ((subs prop_02), "(vrai et faux)");
  ((subs prop_03), "non (vrai)");
  ((subs prop_04), "(vrai ou faux)");
  ((subs prop_05), "(faux implique (vrai ou faux))");
  ((subs prop_06), "(2 = 4)");
  ((subs prop_07), "((3 + 5) = (2 * 4))");
  ((subs prop_08), "((2 * (3 * (k + 2))) = ((k + 2) + 1))");
  ((subs prop_09), "((3 + (3 * (k + 2))) <= (4 * (k + 2)))");
  ((subs prop_10), "((5 <= 7) et ((8 + 9) <= (4 * 5)))");
  ((subs prop_11), "(((3 * (k + 2)) = 1) implique ((k + 2) <= 0))");
] (prop_to_string)
;;

(** 1.4.4 Les triplets de Hoare *)

(* Question 8. *)
type hoare_triple = t_prop * prog * t_prop;;

(* Question 9. *)

(* {x = 2} skip {x = 2} *) 
let hoare_01 = (
  Equal(Var("x"), Const(2)), 
  Skip, 
  Equal(Var("x"), Const(2)))
;;

(* {x = 2} x := 3 {x <= 3} *)
let hoare_02 = (
  Equal(Var("x"), Const(2)), 
  Aff("x", Const(3)), 
  Le(Var("x"), Const(3)))
;;

(* {True} if x <= 0 then r := 0-x else r := x {0 <= r} *)
let hoare_03 =
  (
    True,
    Cond
      (
        Le(Var("x"), Const(0)),
        Aff("r", Ope(Const(0),Var("x"),MINUS)),
        Aff("r", Var("x"))
      ),
    Le(Const(0), Var("r"))
  ) 
;;

(* {in = 5 et out = 1} fact {in = 0 et out = 120} *)
let hoare_04 = 
  (
    And(Equal(Var("in"), Const(5)), Equal(Var("out"), Const(1))),
    prog_fact,
    And(Equal(Var("in"), Const(0)), Equal(Var("out"), Const(120)))
  )
;;

(** 1.4.5 Validité d’un triplet de Hoare *)

(* Question 10. *)
let htvalid_test (ht : hoare_triple) (v : valuation) : bool =
  let (pre, p, post) : t_prop * prog * t_prop = ht in
  if pinterp pre v
  then (
    let valuation_res = exec p v in
    pinterp post valuation_res
  )
  else false 
;;

Printf.printf "%B\n" (htvalid_test hoare_01 [("x", 2)]);;
Printf.printf "%B\n" (htvalid_test hoare_01 [("x", 3)]);;
Printf.printf "%B\n" (htvalid_test hoare_02 [("x", 2)]);;
Printf.printf "%B\n" (htvalid_test hoare_03 [("x", 0)]);;
Printf.printf "%B\n" (htvalid_test hoare_03 [("x", 1)]);;
Printf.printf "%B\n\n" (htvalid_test hoare_04 [("in", 5); ("out", 1)]);;


(** 2. Un (mini) prouveur en logique de Hoare*)

(** 2.1 Les buts de preuves et le langage des tactiques *)

(** 2.1.1 Les buts de preuves *)

(* Question 1. *)

type context = (string * t_prop) list;;

type conclusion =
  | Hoare of hoare_triple
  | Prop of t_prop
;;

type goal = context * conclusion;;

(* Question 2. *)

let prop_P : t_prop = True;;
let prop_Q : t_prop = False;;
let prop_R : t_prop = True;;

let goal_01 : goal = (
  [("H", Impl(Or(prop_P, prop_Q), prop_R)); ("H2", prop_P)],
  Prop(Or(prop_P, prop_Q))
);;

let goal_02 : goal = (
  [],
  Hoare(
    Equal(Var("x"), Const(-3)),
    Cond(
      Le(Var("x"), Const(0)),
      Aff("x", Ope(Const(0), Var("x"), MINUS)),
      Aff("x", Var("x"))
    ),
    Equal(Var("x"), Const(3))
  )
);;

(* Question 3. *)

let print_goal (g : goal) : unit =
  let (ct, cc) : context * conclusion = g in
  List.iter (fun (v, p) -> Printf.printf "%s : %s\n" v (prop_to_string p)) ct;
  Printf.printf "===================================\n";
  match cc with
  | Hoare(h) -> (
      let (pre, prog, post) : t_prop * prog * t_prop = h in
      Printf.printf "{ %s }\n" (prop_to_string pre);
      Printf.printf "%s\n" (prog_to_string prog);
      Printf.printf "{ %s }\n\n" (prop_to_string post);
    )
  | Prop(p) -> Printf.printf "%s\n\n" (prop_to_string p);
;;

print_goal goal_01;;
print_goal goal_02;;

let fresh_ident =
  let prefix = "H" and count = ref 0
  in
  function () -> (count := !count + 1 ;
                  prefix ^ (string_of_int (!count)))
;;

let h1 = fresh_ident();;
let h2 = fresh_ident();;

Printf.printf "(%s, %s)\n\n" h1 h2;;

(** 2.1.2 La règle de déduction pour la boucle *)

(* Question 4. *)

(* 

  Arbre de preuve ???

  Est-ce qu'il veut un arbre comme ca :

https://fr.wikiversity.org/wiki/Logique_des_propositions/D%C3%A9finitions#/media/Fichier:Logique2.jpg

    ????

*)

(* Question 5. *)

(* TODO *)

(** 2.1.3 Le langage des tactiques *)

(* Question 6. *)

type tactic =
  (* Partie logique des propositions *)
  | And_Intro 
  | Or_Intro_1
  | Or_Intro_2
  | Impl_Intro
  | Not_Intro
  | And_Elim_1 of string
  | And_Elim_2 of string
  | Or_Elim of string
  | Impl_Elim of string * string
  | Not_Elim of string * string
  | Exact of string
  | Assume of t_prop
  (* 
  | Admit of ??
*)
  (* Partie logique de Hoare *)
  | HSkip
  | HAssign
  | HIf
  | HRepeat of string
  | HCons of t_prop * t_prop
  | HSeq of t_prop
;;

(** 2.2 Appliquer une tactique à un but *)

(* Question 1. *)

let rec bool2prop (be : bexp) : t_prop  =
  match be with
  | True -> True
  | False -> False
  | Not(b) -> Not(bool2prop(b))
  | And(b1, b2) -> And(bool2prop(b1), bool2prop(b2))
  | Or(b1, b2) -> Or(bool2prop(b1), bool2prop(b2))
  | Equal(a1, a2) -> Equal(a1, a2)
  | Le(a1, a2) -> Le(a1, a2)
;;

Printf.printf "%s\n" (prop_to_string(bool2prop(bexp_01)));;
Printf.printf "%s\n" (prop_to_string(bool2prop(bexp_09)));;

(* Question 2. *)

let find_prop_context (name : string) (c : context) : t_prop = 
  try 
    (
      let _, value = List.find (fun (x, _) -> String.equal name x) c in
      value
    )
  with | _ -> failwith ("No such hypothesis: " ^ name)
;;

let apply_tactic (t : tactic) (g : goal) : goal list =
  let (ct, cc) : context * conclusion = g in
  match t with
  | And_Intro -> (
      match cc with 
      | Prop(And(p1, p2)) -> [(ct, Prop(p1)); (ct, Prop(p2))]
      | _ -> failwith "Tactic failure: Goal is not an And-formula."
    )
  | Or_Intro_1 -> (
      match cc with 
      | Prop(Or(p1, p2)) -> [(ct, Prop(p1))]
      | _ -> failwith "Tactic failure: Goal is not an Or-formula."
    )
  | Or_Intro_2 -> (
      match cc with 
      | Prop(Or(p1, p2)) -> [(ct, Prop(p2))]
      | _ -> failwith "Tactic failure: Goal is not an Or-formula."
    )
  | Impl_Intro -> (
      match cc with 
      | Prop(Impl(p1, p2)) -> [((fresh_ident(), p1)::ct, Prop(p2))]
      | _ -> failwith "Tactic failure: Goal is not an Impl-formula."
    )
  | Not_Intro -> (
      match cc with 
      | Prop(Not(p1)) -> [((fresh_ident(), p1)::ct, Prop(False))]
      | _ -> failwith "Tactic failure: Goal is not an Not-formula."
    )
  | And_Elim_1(h) -> (
      match (find_prop_context h ct) with 
      | And(p1, p2) -> [((fresh_ident(), p1)::ct, cc)]
      | _ -> failwith "Tactic failure: Hypothesis is not an And-formula."
    )
  | And_Elim_2(h) -> (
      match (find_prop_context h ct) with 
      | And(p1, p2) -> [((fresh_ident(), p2)::ct, cc)]
      | _ -> failwith "Tactic failure: Hypothesis is not an And-formula."
    )
  | Or_Elim(h) -> (
      match (find_prop_context h ct) with 
      | Or(p1, p2) -> [((fresh_ident(), p1)::ct, cc); ((fresh_ident(), p2)::ct, cc)]
      | _ -> failwith "Tactic failure: Hypothesis is not an Or-formula."
    )
  | Impl_Elim(h1, h2) -> (
      match (find_prop_context h1 ct) with 
      | Impl(h1_1, h1_2) -> 
          if h1_1 = (find_prop_context h2 ct) 
          then [((fresh_ident(), h1_2)::ct, cc)]
          else failwith "Tactic failure: Second hypothesis does not match the assumption of the first hypothesis."
      | _ -> failwith "Tactic failure: Hypothesis is not an Impl-formula."
    )
  | Not_Elim(h1, h2) -> (
      match (find_prop_context h1 ct) with 
      | Not(h1_1) -> 
          if h1_1 = (find_prop_context h2 ct) 
          then [((fresh_ident(), False)::ct, cc)]
          else failwith "Tactic failure: Second hypothesis does not match the body of the first hypothesis."
      | _ -> failwith "Tactic failure: Hypothesis is not an Not-formula."
    )
  | Exact(h) -> (
      match cc with
      | Prop(p) -> 
          if (find_prop_context h ct) = p
          then [] (*WIN*)
          else failwith "Tactic failure: Props are not the same."
      | _ -> failwith "Tactic failure: The conclusion is not a logical proposition."
    
    )
  | Assume(p) -> (
      [((fresh_ident(), p)::ct, cc); (ct, Prop(p))]
    )
  | HSkip -> (
    match cc with
    | Hoare(pre, prog, pos) -> (
      match prog with
      | Skip -> (
        if (pre = pos)
        then [] (*WIN*)
        else failwith "Precondiction is not right"
      )
      | _ -> failwith "Goal is not a Skip-statement"
    )
    | _ -> failwith "Goal is not a Hoare formula"
  )
  | HAssign -> (
    match cc with
    | Hoare(pre, prog, pos) -> (
      match prog with
      | Aff(s, v) -> (
        []
      )
      | _ -> failwith "Goal is not an assignment"
    )
    | _ -> failwith "Goal is not a Hoare formula"
  )
  (* 
  | Admit(??)  
| HAssign
| HIf
| HRepeat(v)
| HCons(pre, post)
| HSeq(p)
  *)
  | _ -> failwith "Not supported yet.."
;;

(** 2.2.1 La logique des propositions *)
(* Question 3. *)

(* (P V Q => R) => (P => R) ^ (Q => R) *)
let goal_q3 : goal = (
  [],
  Prop(
    Impl(
      Impl(Or(prop_P, prop_Q), prop_R), 
      And(Impl(prop_P, prop_R), 
          Impl(prop_Q, prop_R))
    )
  )
);;


print_goal goal_q3;;

(* Impl_Intro. *)
let goal_q3 = List.hd (apply_tactic Impl_Intro goal_q3);;

(* And_Intro. *)
let goal_q3_list = apply_tactic And_Intro goal_q3;;
let goal_q3_1 = List.nth goal_q3_list 0;; (* P -> R *)
print_goal goal_q3_1;;
let goal_q3_3 = List.nth goal_q3_list 1;; (* Q -> R *)
print_goal goal_q3_3;;

(* Impl_Intro. *)
let goal_q3_1 = List.hd (apply_tactic Impl_Intro goal_q3_1);;
print_goal goal_q3_1;;

(* assume (P \/ Q). *)
let goal_q3_list = apply_tactic (Assume(Or(prop_P, prop_Q))) goal_q3_1;;
let goal_q3_1 = List.nth goal_q3_list 0;; (* R *)
print_goal goal_q3_1;;
let goal_q3_2 = List.nth goal_q3_list 1;; (* P \/ Q *)
print_goal goal_q3_2;;

(* Impl_Elim in H and H1. *)
let goal_q3_1 = List.hd (apply_tactic (Impl_Elim("H3","H5")) goal_q3_1);;
print_goal goal_q3_1;;

(* exact H2. *)
let goal_q3_1 = apply_tactic (Exact("H6")) goal_q3_1;; (* fini car liste vide *)
                                                       
(* Or_Intro_1. *)
let goal_q3_2 = List.hd (apply_tactic (Or_Intro_1) goal_q3_2);;
print_goal goal_q3_2;;
  
(* exact H0.                    *)
let goal_q3_2 = apply_tactic (Exact("H4")) goal_q3_2;; (* fini car liste vide *)

(* Impl_Intro.                  *) 
let goal_q3_3 = List.hd (apply_tactic (Impl_Intro) goal_q3_3);;
print_goal goal_q3_3;;

(* assume (P \/ Q).          LA *)
let goal_q3_list = apply_tactic (Assume(Or(prop_P, prop_Q))) goal_q3_3;;
let goal_q3_3 = List.nth goal_q3_list 0;; (* R *)
print_goal goal_q3_3;;
let goal_q3_4 = List.nth goal_q3_list 1;; (* P \/ Q *)
print_goal goal_q3_4;;

(* Impl_Elim in H and H1.       *)
let goal_q3_3 = List.hd (apply_tactic (Impl_Elim("H3","H8")) goal_q3_3);;
print_goal goal_q3_3;;

(* exact H2.                    *)
let goal_q3_3 = apply_tactic (Exact("H9")) goal_q3_3;; (*fini car liste vide*)

(* Or_Intro_2.                  *)  
let goal_q3_4 = List.hd (apply_tactic (Or_Intro_2) goal_q3_4);;
print_goal goal_q3_4;;

(* exact H0.                    *)
let goal_q3_4 = apply_tactic (Exact("H7")) goal_q3_4;; (*fini car liste vide*) 
                                                       
(** 2.2.2 La logique de Hoare *)

(* Question 4. *)

let goal_q4_1 = apply_tactic HSkip ([], Hoare(hoare_01));;

(* Question 5. *)
