From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics.
From RUXt.types Require Export rules.
From RUXt.model Require Export logic refute.


(*** Properties relating OX and UX reasoning ***)

(* Reasoning principles for triples *)
Theorem principle_of_agreement γ e Pₒₓ λQₒₓ Pᵤₓ Qᵤₓ ε :
  ux_triple γ e Pᵤₓ Qᵤₓ ε →
  ⊨ (Pᵤₓ →ₕ Pₒₓ) →
  ox_triple γ e Pₒₓ λQₒₓ →
  ⊨ (Qᵤₓ →ₕ ∃ₕ v, (⌞ ε = Ok v ⌟ ∗ λQₒₓ v)).
Proof.
  intros Hux HPimp Hox h' HQux.
  apply Hux in HQux as [h [HPux Hstep]].
  apply Hox in Hstep as [?[->]]; last by eapply HPimp.
  do 3 eexists. by repeat split;
    first apply map_union_id_l; first apply map_disjoint_empty_l.
Qed.
Theorem principle_of_denial γ e Pₒₓ λQₒₓ Pᵤₓ Qᵤₓ ε :
  ux_triple γ e Pᵤₓ Qᵤₓ ε →
  ⊨ (Pᵤₓ →ₕ Pₒₓ) →
  ¬ ⊨ (Qᵤₓ →ₕ ∃ₕ v, (⌞ ε = Ok v ⌟ ∗ λQₒₓ v)) →
  ¬ ox_triple γ e Pₒₓ λQₒₓ.
Proof.
  intros Hux HPimp HnQimp Hox. apply HnQimp.
  by eapply principle_of_agreement.
Qed.

(* Reasoning principles under type specification contexts *)
Definition valid_pre τs vs P := ⊨ (P →ₕ [∗ₜ vs [⊲] boxes τs]).
Definition valid_library Λ := valid_type_ctx (impls Λ) (types Λ).
Theorem principle_of_validity Λ L τ Q ε :
  valid_library Λ → derivable_post Λ L valid_pre τ Q ε →
  ⊨ (Q →ₕ (∃ₕ v, (⌞ ε = Ok v ⌟ ∗ [∗ₜ [v ⊲ box τ]]))).
Proof.
  intros HenvT [f [τs [Htype [vs [P [HP [xs [e [Himpl Hspec]]]]]]]]].
  (* Obtain the UX triple *)
  apply ux_soundness in Hspec as Hux.
  (* Obtain the OX triple *)
  eapply HenvT in Htype as [? [? [HFimpl' Hox]]].
  rewrite HFimpl' in Himpl; inversion Himpl; subst.
  (* The goal follows from the principle of agreement *)
  by eapply principle_of_agreement.
Qed.
Definition ub_derivable Λ :=
  ∃ L τ Q ε, derivable_post Λ L valid_pre τ Q ε ∧ sat Q ∧ ¬ ∃ v, ε = Ok v.
Theorem type_unsoundness Λ :
  ub_derivable Λ → ¬ valid_library Λ.
Proof.
  intros [?[?[?[?[Hpost [Hsat Hε]]]]]] Hvalid.
  eapply principle_of_validity in Hvalid; try done. apply Hsat.
  intros h [?[?[?[?[?[[_ ?] _]]]]]]%Hvalid. by apply Hε; eexists.
Qed.
