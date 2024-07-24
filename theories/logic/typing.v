From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.
From RUXt.lang Require Import semantics.
From RUXt.assertion Require Export hprop.
From RUXt.assertion.types Require Export int bool unit own.


(*** Over-approximate specifications ***)

(* Function types *)
Record fun_type := mk_fun_type { ty_in : list type; ty_out : type }.
Notation "{ τs ↣ τ }" := (mk_fun_type τs τ).
Definition type_ctx := gmap string fun_type.

(* Typing rules *)
Reserved Notation "Δ ∣ 𝕋 ⊢ e ⊣ λ𝕌" (at level 50).
Inductive ty_rule : type_ctx → (list typing) → expr → (val → list typing) → Prop :=
| T_Int Δ z :
  Δ ∣ [] ⊢ Pure (PInt z) ⊣ λ v, [v ⊲ int]
| T_Bool Δ b :
  Δ ∣ [] ⊢ Pure (PBool b) ⊣ λ v, [v ⊲ bool]
| T_Unit Δ :
  Δ ∣ [] ⊢ Pure PUnit ⊣ λ v, [v ⊲ unit]
| T_Let Δ x e1 e2 𝕋 λ𝕌 λ𝕍 :
  Δ ∣ 𝕋 ⊢ e1 ⊣ λ𝕍 → (∀ v, Δ ∣ λ𝕍 v ⊢ e2⌊v//x⌋ ⊣ λ𝕌) →
  Δ ∣ 𝕋 ⊢ Let x e1 e2 ⊣ λ𝕌
| T_Call Δ f ts τs τ vs :
  Δ !! f = Some {τs ↣ τ} → ts = TVals vs →
  Δ ∣ vs [⊲] boxes τs ⊢ Call f ts ⊣ λ v, [v ⊲ box τ]
where "Δ ∣ 𝕋 ⊢ e ⊣ λ𝕌" := (ty_rule Δ 𝕋 e λ𝕌).


(*** Soundness ***)

(* OX rule definition *)
Definition ox_triple (γ : impl_ctx) (e : expr) (P : hprop) (λQ : val → hprop) : Prop :=
  ∀ h, P h → ∀ h' ε, γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩ → ∃ v, λQ v h' ∧ ε = Ok v.
Definition valid_types (γ : impl_ctx) (Δ : type_ctx) : Prop :=
  ∀ f τs τ, Δ !! f = Some {τs ↣ τ} → ∃ xs e, γ !! f = Some {(xs) e} ∧
  ∀ vs, ox_triple γ (e⌊vs[//]xs⌋) ([∗ₜ vs [⊲] boxes τs]) (λ v, [∗ₜ [v ⊲ box τ]]).
Definition ty_spec (Δ : type_ctx) (e : expr) (𝕋 : list typing) (λ𝕌 : val → list typing) : Prop :=
  ∀ γ, valid_types γ Δ → ox_triple γ e ([∗ₜ 𝕋]) (λ v, [∗ₜ λ𝕌 v]).

(* Soundness of typing rules *)
Theorem ty_soundness Δ 𝕋 e λ𝕌 :
  Δ ∣ 𝕋 ⊢ e ⊣ λ𝕌 → ty_spec Δ e 𝕋 λ𝕌.
Proof.
  intros rule; induction rule.
  + intros γ Hval h HP h' ε Hstep. inversion Hstep; subst.
    exists (VInt z). by split; first apply hiter_singleton.
  + admit.
  + admit.
  + intros γ Hval h H𝕋 h' ε Hstep. inversion Hstep; subst.
    - assert (∀ v, ty_spec Δ (e2⌊v//x⌋) (λ𝕍 v) λ𝕌) as IHrule' by assumption.
      assert (γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h'' | Ok v ⟩) as Hstep1 by assumption.
      specialize (IHrule _ Hval _ H𝕋 _ _ Hstep1) as [v1 [H𝕍 Hok]].
      inversion Hok; subst. by eapply IHrule'.
    - assert (γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | Err ξ ⟩) as Hstep1 by assumption.
      specialize (IHrule _ Hval _ H𝕋 _ _ Hstep1) as [v1 [H𝕍 Hok]].
      by exfalso.
    - assert (γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | Miss m ⟩) as Hstep1 by assumption.
      specialize (IHrule _ Hval _ H𝕋 _ _ Hstep1) as [v1 [H𝕍 Hok]].
      by exfalso.
  + intros γ Hval h HP h' ε Hstep. inversion Hstep; subst.
    - specialize (Hval _ _ _ H) as [? [? [Hsome' Hox]]].
      assert (γ !! f = Some { (xs) e}) as Hsome by assumption.
      rewrite Hsome' in Hsome; inversion Hsome; subst.
      by eapply Hox.
    - specialize (Hval _ _ _ H) as [xs [e [Hsome _]]].
      by rewrite Hsome in *.
Admitted.
