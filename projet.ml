(** 
  Un interpréteur pour un langage imperatif et un prouveur en logique de Hoare 
  et un prouveur en logique de Hoare.
  @author Frejoux Gaetan, Niord Mathieu, Sauzeau Yannis
*)

(** 1. Un interpreteur pour un langage imperatif *)
(** 1.1 Les expressions arithmetiques *)
(** 1.1.1 Syntaxe abstraite*)

(** Question 1.*)
type aexp = NILL;;

(** Question 2.*)
(** 2 *)
let a = 0;;
(** 2 + 3, 2 - 5, 3 * 6 *)
let a = 0;;
let a = 0;;
let a = 0;;
(** 2 + x, 4 * y, 3 * x * x, 5 * x + 7 * y, 6 * x + 5 * y * x *)
let a = 0;;
let a = 0;;
let a = 0;;
let a = 0;;


(** Question 3. *)
(**1.*)
let aexp_to_string (e : aexp) : string = "";;

(**2.*)
(** 2 *)
let a = 0;;
(** 2 + 3, 2 −5, 3 * 6 *)
let a = 0;;
let a = 0;;
let a = 0;;
(** 2 + x, 4 * y, 3 * x * x, 5 * x + 7 * y, 6 * x + 5 * y * x *)
let a = 0;;
let a = 0;;
let a = 0;;
let a = 0;;



(** 1.1.2 Interprétation *)

(** Question 4. *)
type valuation = NILL;;

(** Question 5. *)
let ainterp (e : aexp) (v : valuation) : int = 0;;

(** Question 6. *)
(** x = 5 et y = 9 *)
let val_1_1_2 = NILL;;

(** 2 *)
ainterp (NILL) (val_1_1_2);;

(** 2 + 3, 2 −5, 3 * 6 *)
ainterp (NILL) (val_1_1_2);;
ainterp (NILL) (val_1_1_2);;
ainterp (NILL) (val_1_1_2);;

(** 2 + x, 4 * y, 3 * x * x, 5 * x + 7 * y, 6 * x + 5 * y * x *)
ainterp (NILL) (val_1_1_2);;
ainterp (NILL) (val_1_1_2);;
ainterp (NILL) (val_1_1_2);;
ainterp (NILL) (val_1_1_2);;



(** 1.1.3 Substitutions *)

(** Question 7. *)
let asubst (n : char) (s : aexp) (e : aexp) : aexp = NILL;;

(** Question 8. *)
(**TODO flemme de réécrire tout *)


(** 1.2 Les expressions booléennes *)

(** 1.2.1 Syntaxe abstraite *)
(** 1.2.2 Interprétation *)

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