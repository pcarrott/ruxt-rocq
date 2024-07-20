From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.
From RUXt.lang Require Import semantics.
From RUXt.assertion Require Export hprop.
From RUXt.assertion.types Require Export own.


(*** Over-approximate specifications ***)

(* Function types *)
Record fun_type := mk_fun_type { ty_in : list type; ty_out : type }.
Notation "{ τs ↣ τ }" := (mk_fun_type τs τ).
Definition type_ctx := gmap string fun_type.

(* Typing judgements *)
Reserved Notation "Δ ∣ 𝕋 ⊢ e ⊣ v , 𝕌" (at level 50).


(*** Soundness ***)

(* OX rule definition *)
Definition ox_triple (γ : impl_ctx) (e : expr) (P Q : hprop) (v : val) : Prop :=
  ∀ h, P h → ∀ h' ε, γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩ → Q h' ∧ ε = Ok v.
Definition valid_types (γ : impl_ctx) (Δ : type_ctx) : Prop :=
  ∀ f τs τ, Δ !! f = Some {τs ↣ τ} → ∃ xs e, γ !! f = Some {(xs) e} ∧
  ∀ vs, ∃ v, ox_triple γ (e⌊vs[//]xs⌋) [∗ vs [⊲] own_vals τs] [∗ [v ⊲ own_val τ]] v.
Definition ty_spec (Δ : type_ctx) (e : expr) (𝕋 𝕌 : list typing) (v : val) : Prop :=
  ∀ γ, valid_types γ Δ → ox_triple γ e [∗ 𝕋] [∗ 𝕌] v.
