From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang assertion.


(*** Type system ***)

(* Language types *)
Record type := {
  ty_name : string;
  ty_size : nat;
  ty_own : list val → asrt;
  ty_size_eq vs : ty_own vs ⊨ ⌞ length vs = ty_size ⌟;
}.
Notation "⟦ τ '⟧(' vs )" := (ty_own τ vs).
(* Function types *)
Record fun_type := mk_fun_type { ty_in : list type; ty_out : type }.
Notation "{ τs ↣ τ }" := (mk_fun_type τs τ).
Definition type_ctx := gmap string fun_type.

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