From RUXt.logic Require Export assertion.
From RUXt.lang Require Import semantics.
From RUXt.types Require Import own.
From RUXt.lib Require Import gmap.


(*** Under-approximate specifications ***)

(* Function specifications *)
Record fun_spec := { vals : list value; pre : asrt; tag : exit; post : asrt }.
Notation "[ ( vs ) P | ε , Q ]" := {| vals := vs; pre := P; tag := ε; post := Q |}.
Definition spec_ctx : Set := gmap string fun_spec.
(* UX triples *)
Definition ux_triple (γ : impl_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  ∀ θ h', eval_asrt θ h' Q → ∃ h, eval_asrt θ h P ∧ (γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩).
Definition valid_specs (γ : impl_ctx) (Γ : spec_ctx) : Prop :=
  ∀ f s, Γ !! f = Some s → ∃ i e, γ !! f = Some i ∧
  subst_l (params i) (vals s) (body i) = Some e ∧
  ux_triple γ e (pre s) (post s) (tag s).
Definition ux_spec (Γ : spec_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  ∀ γ, valid_specs γ Γ → ux_triple γ e P Q ε.
Notation "Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉" := (ux_spec Γ e P Q ε)
  (at level 100, no associativity).


(*** Over-approximate specifications ***)

(* Function types *)
Record fun_type := { ty_in : list type; ty_out : type }.
Notation "{ τs ↣ τ }" := {| ty_in := τs; ty_out := τ |}.
Definition type_ctx : Set := gmap string fun_type.
(* Typing judgements *)
Definition ox_triple (γ : impl_ctx) (e : expr) (P Q : asrt) (v : value) : Prop :=
  ∀ θ h, eval_asrt θ h P → ∀ h' ε, (γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩) → eval_asrt θ h' Q ∧ ε = Ok v.
Definition valid_types (γ : impl_ctx) (Δ : type_ctx) : Prop :=
  ∀ f t, Δ !! f = Some t → ∃ i, γ !! f = Some i ∧
  ∀ vs e 𝕋, (
    subst_l (params i) vs (body i) = Some e ∧
    to_typing vs (own_ptr <$> (ty_in t)) = Some 𝕋
  ) →
  ∃ v, ox_triple γ e [∗ 𝕋] [∗ [v ⊲ own_ptr (ty_out t)]] v.
Definition ox_spec (Δ : type_ctx) (e : expr) (𝕋 𝕌 : list typing) (v : value) : Prop :=
  ∀ γ, valid_types γ Δ → ox_triple γ e [∗ 𝕋] [∗ 𝕌] v.
Notation "Δ | 𝕋 ⊢ e ⊣ v , 𝕌" := (ox_spec Δ e 𝕋 𝕌 v)
  (at level 100, no associativity).
