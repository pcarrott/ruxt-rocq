From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics assertion.

(* UX semantics *)
Definition ux_triple (γ : impl_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  ∀ h', hprop h' Q → ∃ h, hprop h P ∧ γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩.

(* The refutation algorithm requires a logic that derives UX specifications *)
Record logic := {
  derivable_spec : impl_ctx → expr → asrt → asrt → exit → Prop;
  ux_soundness γ e P Q ε : derivable_spec γ e P Q ε → ux_triple γ e P Q ε;
}.

(* UX properties *)
Lemma pure_spec γ v :
  ux_triple γ (Pure (PVal v)) EMP EMP (Ok v).
Proof.
  intros ? ?. eexists.
  by split; last apply O_Pure.
Qed.
Lemma let_spec γ x e1 e2 P Q R v ε :
  ux_triple γ e1 P R (Ok v) → ux_triple γ (e2⌊v//x⌋) R Q ε →
  ux_triple γ (Let x e1 e2) P Q ε.
Proof.
  intros Hux1 Hux2 ? [?[[?[]]%Hux1]]%Hux2. eexists.
  by split; last eapply O_Let.
Qed.
Lemma frame_spec γ e P Q v :
  ux_triple γ e EMP Q (Ok v) →
  ux_triple γ e P (P ∗ Q) (Ok v).
Proof.
  intros Hux ? [hP [hQ [-> [?[? [?[-> Hstep]]%Hux]]]]]. eexists.
  split; last eapply frame_addition in Hstep as [[Hstep]|[?[]]]; try done.
  by rewrite (map_empty_union hP), (map_union_comm hQ hP) in Hstep.
Qed.
Lemma call_spec γ f xs e vs P Q ε :
  ux_triple γ (e ⌊ vs [//] xs ⌋) P Q ε → γ !! f = Some { (xs) e} →
  ux_triple γ (Call f (TVals vs)) P Q ε.
Proof.
  intros Hux ? ? [?[]]%Hux.
  eexists. by split; last eapply O_Call.
Qed.
