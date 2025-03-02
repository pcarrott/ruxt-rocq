From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics assertion.

(* UX semantics *)
Definition ux_triple eval (γ : impl_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  ∀ h', hprop h' Q → ∃ h, hprop h P ∧ eval γ h e h' ε.
Definition ux_frame_triple γ e P Q ε := ux_triple eval_expr_frame γ e P Q ε.
Definition ux_full_triple γ e P Q ε := ux_triple eval_expr γ e P Q ε.
Theorem ux_triple_preservation γ e P Q ε :
  ux_frame_triple γ e P Q ε → ux_full_triple γ e P Q (exit_in_full ε).
Proof.
  intros Hux ? [?[? ?%semantics_preservation]]%Hux. by eexists.
Qed.

(* The refutation algorithm requires a logic that derives UX specifications *)
Record logic := {
  derivable_spec : impl_ctx → expr → asrt → asrt → exit → Prop;
  ux_frame_soundness γ e P Q ε : 
    derivable_spec γ e P Q ε → ux_frame_triple γ e P Q ε;
}.
Corollary ux_soundness L γ e P Q ε :
  (derivable_spec L) γ e P Q ε → ux_full_triple γ e P Q (exit_in_full ε).
Proof.
  by intros ?%ux_frame_soundness%ux_triple_preservation.
Qed.

(* UX properties *)
Lemma pure_spec γ v :
  ux_frame_triple γ (Pure (PVal v)) EMP EMP (Ok v).
Proof.
  intros ? ?. eexists.
  by split; last apply F_Pure.
Qed.
Lemma let_spec γ x e1 e2 P Q R v ε :
  ux_frame_triple γ e1 P R (Ok v) → ux_frame_triple γ (e2⌊v//x⌋) R Q ε →
  ux_frame_triple γ (Let x e1 e2) P Q ε.
Proof.
  intros Hux1 Hux2 ? [?[[?[]]%Hux1]]%Hux2. eexists.
  by split; last eapply F_Let.
Qed.
Lemma frame_spec γ e P Q v :
  ux_frame_triple γ e EMP Q (Ok v) →
  ux_frame_triple γ e P (P ∗ Q) (Ok v).
Proof.
  intros Hux ? [hP [hQ [-> [?[? [?[-> Hstep]]%Hux]]]]]. eexists.
  split; last eapply frame_addition in Hstep as [[Hstep]|[?[]]]; try done.
  by rewrite (map_empty_union hP), (map_union_comm hQ hP) in Hstep.
Qed.
Lemma call_spec γ f xs e vs P Q ε :
  γ !! f = Some { (xs) e} →
  ux_frame_triple γ (Call f (TVals vs)) P Q ε ↔ ux_frame_triple γ (e ⌊ vs [//] xs ⌋) P Q ε.
Proof.
  intros HSome. split.
  + intros Hux ? [?[? Hcall]]%Hux.
    inversion Hcall; rewrite H4 in HSome; inversion HSome; subst.
    by eexists.
  + intros Hux ? [?[]]%Hux.
    eexists. by split; last eapply F_Call.
Qed.
