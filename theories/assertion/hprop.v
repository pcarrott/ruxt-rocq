From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.
From RUXt.lang Require Import semantics.


(*** Assertion language ***)

(* Heap predicates *)
Definition hprop := heap → Prop.

Definition hpure (P : Prop) : hprop := λ h, h = ∅ ∧ P.
Notation "⌜ P ⌝" := (hpure P).
Definition hand (H1 H2 : hprop) : hprop := λ h, H1 h ∧ H2 h.
Notation "H1 ∧∧ H2" := (hand H1 H2) (at level 50).
Definition hor (H1 H2 : hprop) : hprop := λ h, H1 h ∨ H2 h.
Notation "H1 ∨∨ H2" := (hor H1 H2) (at level 50).
Definition himplies (H1 H2 : hprop) : hprop := λ h, H1 h → H2 h.
Notation "H1 ⇒ H2" := (himplies H1 H2) (at level 50).
Definition hnot (H : hprop) : hprop := λ h, ¬ H h.
Notation "¬¬ H" := (hnot H) (at level 50).
Definition hexists {X : Type} (P : X → hprop) : hprop := λ h, ∃ x, P x h.
Notation "∃∃ x , H" := (hexists (λ x, H)) (at level 50).
Notation "∃∃ x ⋮ X , H" := (hexists (λ x : X, H)) (at level 50).

Definition hpure_eq (p1 p2 : pure) : hprop := λ h, h = ∅ ∧
  ∃ v, ⌊ p1 ⌋ₚ = Ok v ∧ ⌊ p1 ⌋ₚ = ⌊ p2 ⌋ₚ.
Notation "⌞ p1 == p2 ⌟" := (hpure_eq p1 p2).
Definition hpure_true (p : pure) : hprop := λ h, h = ∅ ∧
  ⌊ p ⌋ₚ = Ok (VBool true).
Notation "⌞ p ⌟" := (hpure_true p).

Definition hempty : hprop := λ h, h = ∅.
Notation "'emp'" := hempty.
Definition hsingle (p1 p2 : pure) : hprop := λ h,
  ∃ l v, ⌊ p1 ⌋ₚ = Ok (VLoc l) ∧ ⌊ p2 ⌋ₚ = Ok v ∧ h = {[l := LangVal v]}.
Notation "p1 ↦ p2" := (hsingle p1 p2) (at level 50).
Definition hfreed (p : pure) : hprop := λ h,
  ∃ l, ⌊ p ⌋ₚ = Ok (VLoc l) ∧ h = {[l := Freed]}.
Notation "p '↦∅'" := (hfreed p) (at level 50).
Definition huninit (p : pure) : hprop := λ h,
  ∃ l, ⌊ p ⌋ₚ = Ok (VLoc l) ∧ h = {[l := Poison]}.
Notation "p '↦?'" := (huninit p) (at level 50).
Definition hstar (H1 H2 : hprop) : hprop := λ h,
  ∃ h1 h2, h = h1 ∪ h2 ∧ h1 ##ₘ h2 ∧ H1 h1 ∧ H2 h2.
Notation "H1 ∗ H2" := (hstar H1 H2) (at level 50).
Definition hiter {X : Type} (xs : list X) (P : X → hprop) : hprop := 
  foldr hstar emp (P <$> xs).
Notation "'[∗' xs , P ]" := (hiter xs P) (at level 50).

Definition hentails (H1 H2 : hprop) : Prop := ∀ h, H1 h → ∃ h', H2 h' ∧ h' ⊆ h.
Notation "H1 ⊢ H2" := (hentails H1 H2) (at level 50).
Definition hassert (H : hprop) : Prop := ∀ h, H h.
Notation "⊢ H" := (hassert H) (at level 50).
