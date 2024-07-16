From RUXt.lang Require Export lang.
From RUXt.lang Require Import semantics.
From RUXt.lib Require Import gmap.


(*** Assertion language ***)

(* Heap predicates *)
Definition hprop := heap → Prop.

Definition hpure (P : Prop) : hprop := λ h, h = ∅ ∧ P.
Notation "⌜ P ⌝" := (hpure P).
Definition hand (H1 H2 : hprop) : hprop := λ h, H1 h ∧ H2 h.
Notation "H1 ∧∧ H2" := (hand H1 H2) (at level 100).
Definition hor (H1 H2 : hprop) : hprop := λ h, H1 h ∨ H2 h.
Notation "H1 ∨∨ H2" := (hor H1 H2) (at level 100).
Definition himplies (H1 H2 : hprop) : hprop := λ h, H1 h → H2 h.
Notation "H1 ⇒ H2" := (himplies H1 H2) (at level 100).
Definition hnot (H : hprop) : hprop := λ h, ¬ H h.
Notation "¬¬ H" := (hnot H) (at level 100).
Definition hexists {X : Type} (P : X → hprop) : hprop := λ h, ∃ x, P x h.
Notation "∃∃ x , H" := (hexists (λ x, H)) (at level 100).
Notation "∃∃ x ⋮ X , H" := (hexists (λ x : X, H)) (at level 100).

Definition hpure_eq (p1 p2 : pure) : hprop := λ h, h = ∅ ∧
  ∃ v, pure_to_exit p1 = Ok v ∧ pure_to_exit p1 = pure_to_exit p2.
Notation "⌞ p1 == p2 ⌟" := (hpure_eq p1 p2).
Definition hpure_true (p : pure) : hprop := λ h, h = ∅ ∧
  pure_to_exit p = Ok (VBool true).
Notation "⌞ p ⌟" := (hpure_true p).

Definition hempty : hprop := λ h, h = ∅.
Notation "'emp'" := hempty.
Definition hsingle (p1 p2 : pure) : hprop := λ h,
  ∃ l v, pure_to_exit p1 = Ok (VLoc l) ∧ pure_to_exit p2 = Ok v ∧ h = {[l := LangVal v]}.
Notation "p1 ↦ p2" := (hsingle p1 p2) (at level 100).
Definition hfreed (p : pure) : hprop := λ h,
  ∃ l, pure_to_exit p = Ok (VLoc l) ∧ h = {[l := Freed]}.
Notation "p '↦∅'" := (hfreed p) (at level 100).
Definition huninit (p : pure) : hprop := λ h,
  ∃ l, pure_to_exit p = Ok (VLoc l) ∧ h = {[l := Poison]}.
Notation "p '↦?'" := (huninit p) (at level 100).
Definition hstar (H1 H2 : hprop) : hprop := λ h,
  ∃ h1 h2, h = h1 ∪ h2 ∧ h1 ##ₘ h2 ∧ H1 h1 ∧ H2 h2.
Notation "H1 ∗ H2" := (hstar H1 H2) (at level 100).

Definition hentails (H1 H2 : hprop) : Prop := ∀ h, H1 h → ∃ h', H2 h' ∧ h' ⊆ h.
Notation "H1 ⊢ H2" := (hentails H1 H2) (at level 100).
Definition hassert (H : hprop) : Prop := ∀ h, H h.
Notation "⊢ H" := (hassert H) (at level 100).
