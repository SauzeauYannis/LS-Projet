(** 
  Un interpréteur pour un langage imperatif et un prouveur en logique de Hoare 
  et un prouveur en logique de Hoare.
  @author Frejoux Gaetan, Niord Mathieu & Sauzeau Yannis
*)

open Int
open Bool
open String

(**
Print result and check assertion.
@param wanted : The wanted string
@param exp : The exp_to_string
*)
let print_result (result : string) (wanted : string) : unit =
  assert (String.equal result wanted);
  Printf.printf "\nObtenu :\t%s\nAttendu :\t%s\n" result wanted
;;

(**
Print question header.
@param exercise : Exercise number [int]
@param section  : Section number [int]
@param question : Question number [int]
*)
let print_header (exercise : int) (section : int) (question : int) : unit =
  Printf.printf ("\n=== EXERCICE %d, Partie %d : Question %d ===\n\n") exercise section question
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
  print_header (exercise) (section) (question);
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
type aexp = Const of int | Var of string | Ope of aexp * aexp * operator;;

(* Question 2. *)

(* (2) *)
let q2_01 = Const(2);;

(* (2 + 3) *)
let q2_02 = Ope(Const(2), Const(3), ADD);;

(* (2 - 5) *)
let q2_03 = Ope(Const(2), Const(5), MINUS);;

(* (3 * 6) *)
let q2_04 = Ope(Const(3), Const(6), MULT);;

(* (2 + x) *)
let q2_05 = Ope(Const(2), Var("x"), ADD);;

(* (4 * y) *)
let q2_06 = Ope(Const(4), Var("y"), MULT);;

(* (3 * x * x) *)
let q2_07 = Ope(
              Ope(Const(3), Var("x"), MULT),
              Var("x"),
              MULT
            )
;;

(* (5 * x + 7 * y) *)
let q2_08 = Ope(
              Ope(Const(5), Var("x"), MULT),
              Ope(Const(7), Var("y"), MULT),
              ADD
            )
;;

(* (6 * x + 5 * y * x) *)
let q2_09 = Ope(
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
    (q2_01, "2");
    (q2_02, "(2 + 3)");
    (q2_03, "(2 - 5)");
    (q2_04, "(3 * 6)");
    (q2_05, "(2 + x)");
    (q2_06, "(4 * y)");
    (q2_07, "((3 * x) * x)");
    (q2_08, "((5 * x) + (7 * y))");
    (q2_09, "((6 * x) + (5 * (y * x)))");
  ] (aexp_to_string)
;;

(*print_result (aexp_to_string q2_01) "2";;
print_result (aexp_to_string q2_02) "(2 + 3)";;
print_result (aexp_to_string q2_03) "(2 - 5)";;
print_result (aexp_to_string q2_04) "(3 * 6)";;
print_result (aexp_to_string q2_05) "(2 + x)";;
print_result (aexp_to_string q2_06) "(4 * y)";;
print_result (aexp_to_string q2_07) "((3 * x) * x)";;
print_result (aexp_to_string q2_08) "((5 * x) + (7 * y))";;
print_result (aexp_to_string q2_09) "((6 * x) + (5 * (y * x)))";;*)


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
  | _ -> failwith "Cannot compute this expression !"
;;

let var_to_const (var : string) (v : valuation) : int =
  let _, value = List.find (fun (x, y) -> String.equal var x) v in
  value
;;
(**TODO ENVOYER MAIL POUR LA HASHTABLE*)

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
    ((ainterp q2_01 aexp_valuation), "2");
    ((ainterp q2_02 aexp_valuation), "5");
    ((ainterp q2_03 aexp_valuation), "-3");
    ((ainterp q2_04 aexp_valuation), "18");
    ((ainterp q2_05 aexp_valuation), "7");
    ((ainterp q2_06 aexp_valuation), "36");
    ((ainterp q2_07 aexp_valuation), "75");
    ((ainterp q2_08 aexp_valuation), "88");
    ((ainterp q2_09 aexp_valuation), "255");
  ] (Int.to_string)
;;

(*print_result (Int.to_string 2)    (Int.to_string (ainterp q2_01 aexp_valuation));;
print_result (Int.to_string 5)    (Int.to_string (ainterp q2_02 aexp_valuation));;
print_result (Int.to_string (-3)) (Int.to_string (ainterp q2_03 aexp_valuation));;
print_result (Int.to_string 18)   (Int.to_string (ainterp q2_04 aexp_valuation));;
print_result (Int.to_string 7)    (Int.to_string (ainterp q2_05 aexp_valuation));;
print_result (Int.to_string 36)   (Int.to_string (ainterp q2_06 aexp_valuation));;
print_result (Int.to_string 75)   (Int.to_string (ainterp q2_07 aexp_valuation));;
print_result (Int.to_string 88)   (Int.to_string (ainterp q2_08 aexp_valuation));;
print_result (Int.to_string 255)  (Int.to_string (ainterp q2_09 aexp_valuation));;*)


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
    ((subs q2_01), "2");
    ((subs q2_02), "(2 + 3)");
    ((subs q2_03), "(2 - 5)");
    ((subs q2_04), "(3 * 6)");
    ((subs q2_05), "(2 + 7)");
    ((subs q2_06), "(4 * (z + 2))");
    ((subs q2_07), "((3 * 7) * 7)");
    ((subs q2_08), "((5 * 7) + (7 * (z + 2)))");
    ((subs q2_09), "((6 * 7) + (5 * ((z + 2) * 7)))");
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
let bexp_q2_01 : bexp = True;;

(* (vrai et faux) *)
let bexp_q2_02 : bexp = And(True, False);;

(* (non vrai) *)
let bexp_q2_03 : bexp = Not(True);;

(* (vrai ou faux) *)
let bexp_q2_04 : bexp = Or(True, False);;

(* (2 = 4) *)
let bexp_q2_05 : bexp = Equal(Const(2), Const(4));;

(* (3 + 5 = 2 * 4) *)
let bexp_q2_06 : bexp = Equal(
  Ope(Const(3), Const(5), ADD), 
  Ope(Const(2), Const(4), MULT));;

(* (2 * x = y + 1) *)
let bexp_q2_07 : bexp = Equal(
  Ope(Const(2), Var("x"), MULT), 
  Ope(Var("y"), Const(1), ADD));;

(* (5 <= 7) *)
let bexp_q2_08 : bexp = Le(Const(5), Const(7));;

(* (8 + 9 <= 4 * 5) et (3 + x <= 4 * y) *)
let bexp_q2_09 : bexp = And(
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
  | And(l,r) -> "(" ^ (bexp_to_string l) ^ " et " ^ (bexp_to_string r) ^ ")"
  | Or(l,r) -> "(" ^ (bexp_to_string l) ^ " ou " ^ (bexp_to_string r) ^ ")"
  | Equal(l,r) -> "(" ^ (aexp_to_string l) ^ " = " ^ (aexp_to_string r) ^ ")"
  | Le(l,r) -> "(" ^ (aexp_to_string l) ^ " <= " ^ (aexp_to_string r) ^ ")"
;;

(* 3.2 *)
print_header_results 1 2 3 [
    (bexp_q2_01, "vrai");
    (bexp_q2_02, "(vrai et faux)");
    (bexp_q2_03, "non (vrai)");
    (bexp_q2_04, "(vrai ou faux)");
    (bexp_q2_05, "(2 = 4)");
    (bexp_q2_06, "((3 + 5) = (2 * 4))");
    (bexp_q2_07, "((2 * x) = (y + 1))");
    (bexp_q2_08, "(5 <= 7)");
    (bexp_q2_09, "(((8 + 9) <= (4 * 5)) et ((3 + x) <= (4 * y)))");
  ] (bexp_to_string)
;;

(*print_result (bexp_to_string bexp_q2_01) "vrai";;
print_result (bexp_to_string bexp_q2_02) "(vrai et faux)";;
print_result (bexp_to_string bexp_q2_03) "non (vrai)";;
print_result (bexp_to_string bexp_q2_04) "(vrai ou faux)";;
print_result (bexp_to_string bexp_q2_05) "(2 = 4)" ;;
print_result (bexp_to_string bexp_q2_06) "((3 + 5) = (2 * 4))";;
print_result (bexp_to_string bexp_q2_07) "((2 * x) = (y + 1))";;
print_result (bexp_to_string bexp_q2_08) "(5 <= 7)";;
print_result (bexp_to_string bexp_q2_09) "(((8 + 9) <= (4 * 5)) et ((3 + x) <= (4 * y)))";;*)

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
    ((binterp bexp_q2_01 bexp_valuation), "true");
    ((binterp bexp_q2_02 bexp_valuation), "false");
    ((binterp bexp_q2_03 bexp_valuation), "false");
    ((binterp bexp_q2_04 bexp_valuation), "true");
    ((binterp bexp_q2_05 bexp_valuation), "false");
    ((binterp bexp_q2_06 bexp_valuation), "true");
    ((binterp bexp_q2_07 bexp_valuation), "false");
    ((binterp bexp_q2_08 bexp_valuation), "true");
    ((binterp bexp_q2_09 bexp_valuation), "true");
  ] (Bool.to_string)
;;

(*print_result (Bool.to_string (binterp bexp_q2_01 bexp_valuation)) "true";;
print_result (Bool.to_string (binterp bexp_q2_02 bexp_valuation)) "false";;
print_result (Bool.to_string (binterp bexp_q2_03 bexp_valuation)) "false";;
print_result (Bool.to_string (binterp bexp_q2_04 bexp_valuation)) "true";;
print_result (Bool.to_string (binterp bexp_q2_05 bexp_valuation)) "false";;
print_result (Bool.to_string (binterp bexp_q2_06 bexp_valuation)) "true";;
print_result (Bool.to_string (binterp bexp_q2_07 bexp_valuation)) "false";;
print_result (Bool.to_string (binterp bexp_q2_08 bexp_valuation)) "true";;
print_result (Bool.to_string (binterp bexp_q2_09 bexp_valuation)) "true";;*)
 
(** 1.3 Les commandes du langage *)

(** 1.3.1 Syntaxe abstraite *)

(** 1.3.2 Interprétation *)

(** 1.4 Triplets de Hoare et validité *)

(** 1.4.1 Syntaxe abstraite des formules de la logiques des propositions *)
(** 1.4.2 Interprétation *)
(** 1.4.3 Substitutions *)
(** 1.4.4 Les triplets de Hoare *)
(** 1.4.5 Validité d’un triplet de Hoare *)


(** 2. Un (mini) prouveur en logique de Hoare*)

(** 2.1 Les buts de preuves et le langage des tactiques *)

(** 2.1.1 Les buts de preuves *)
(** 2.1.2 La règle de déduction pour la boucle *)
(** 2.1.3 Le langage des tactiques *)

(** 2.2 Les buts de preuves et le langage des tactiques *)

(** 2.2.1 La logique des propositions *)
(** 2.2.2 La logique de Hoare *)
