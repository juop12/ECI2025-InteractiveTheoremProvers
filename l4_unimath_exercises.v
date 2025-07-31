
Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* ~ is infix notation for ~homot~, the type of homotopies between two functions.*)

(* Remember that you can write e.g. ~Locate "~".~ to find information about notation and ~Print negb.~ or ~About negb.~ to find information about a predefined term. *)

Print negb.

Theorem neg_neg_bool: negb ∘ negb ~ idfun bool.
Proof.
  Admitted.

(* Exercise 2 *)

(* Homotopy is transitive. *)

Theorem concat_htpy {A : UU} {B : A → UU} {f g h : ∏ (x : A) , B x} : (f ~ g) → (g ~ h) → (f ~ h).
Proof.
    Admitted.

Infix "~@~" := concat_htpy (at level 70, no associativity).

(* This defines infix notation for concatenation. The stuff in parentheses is not important, but tells Coq the order of operations when it is used in combination with other infix notation.*)

(* Exercise 3 *)

(* Homotopy is associative. *)

(* Hint: use pathsinv0, path_assoc. *)

Theorem assoc_htpy {A : UU} {B : A → UU} {f g h i : ∏ (x : A) , B x} (H : f ~ g) (K : g ~ h) (L : h ~ i) : ((H ~@~ K) ~@~ L) ~ (H ~@~ (K ~@~ L)).
Proof.
    Admitted.

(* Exercise 4 *)

(* When you need to prove a Σ-type, use the command ~use tpair.~ to split the goal into two subgoals.
   When you have a Σ-type as a hypothesis, use ~pr1~ to get the first component of the pair, and ~pr2~ to get the second component of the pair.*)

Theorem unit_iscontr : iscontr unit.
Proof.
    Admitted.

(* Exercise 5 *)

Lemma unit_is_prop (x y : unit) : iscontr (x = y).
Proof.
    Admitted.


(* Exercise 6 *)

(* ~weq A B~ is the type of equivalences from A to B. You can also write ~A ≃ B~ where ≃ is written as ~\simeq~.*)

(* From an equivalence, you can get an inverse function.*)

Theorem inverse {A B : UU} (e : A ≃ B) : B → A.
Proof.
    Admitted.

(* Exercise 7 *)

(* Every contractible type is equivalent to the unit.*)

Theorem contr_equiv_unit {C : UU} {h : iscontr C} : C ≃ unit.
Proof.
    Admitted.

(* Exercise 8 *)

(* The type of paths beginning at the same point is always contractible.*)

Theorem contrthm (A : UU) (a : A) : iscontr (∑ x : A, a = x).
Proof.
  Admitted.