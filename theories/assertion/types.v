From RUXt.lib Require Export gmap.
From RUXt.lang Require Export lang.
From RUXt.assertion Require Export hprop.


(*** Type system ***)
(* TODO: Handle (mut/shr) references and lifetimes *)
(* TODO: Define default types *)

(* Language types *)
Record type := {
  ty_size : nat;
  ty_own : list val → asrt;
  ty_size_eq vs : ty_own vs ⊨ ⌞ length vs = ty_size ⌟;
}.
Notation "⟦ τ '⟧(' vs )" := (ty_own τ vs).

(* Type assignment *)
Inductive typing := TyOwn (v : val) (τ : type).
Notation "v ⊲ τ" := (TyOwn v τ) (at level 50).
Notation "vs [⊲] τs" := (zip_with TyOwn vs τs) (at level 50).
Global Instance TyOwn_eq_inj : Inj2 (=) (=) (=) (TyOwn).
Proof. by injection 1. Qed.

(* Type interpretation *)
Definition own_type (t : typing) : asrt :=
  match t with
  | v ⊲ τ => ⟦τ⟧([v])
  end.
Notation "[∗ₜ 𝕋 ]" := (⌜ [∗ 𝕋, own_type] ⌝) (at level 50).
Lemma own_typings 𝕋 h𝕋 :
  hprop h𝕋 ([∗ 𝕋, own_type]) → hprop h𝕋 ([∗ₜ 𝕋]).
Proof.
  intros. do 2 eexists. by repeat split;
    first apply map_union_id_r; first apply map_disjoint_empty_r.
Qed.