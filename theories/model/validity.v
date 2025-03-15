From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics.
From RUXt.types Require Export rules.
From RUXt.model Require Export logic refute.


(*** Properties relating OX and UX reasoning ***)

(* Reasoning principles for triples *)
Theorem principle_of_agreement eval γ e Pₒₓ λQₒₓ Pᵤₓ Qᵤₓ ε :
  ux_triple eval γ e Pᵤₓ Qᵤₓ ε →
  ⊨ (Pᵤₓ →ₕ Pₒₓ) →
  ox_triple eval γ e Pₒₓ λQₒₓ →
  ⊨ (Qᵤₓ →ₕ ∃ₕ v, (⌞ ε = Ok v ⌟ ∗ λQₒₓ v)).
Proof.
  intros Hux HPimp Hox h' HQux.
  apply Hux in HQux as [h [HPux Hstep]].
  apply Hox in Hstep as [?[->]]; last by eapply HPimp.
  do 3 eexists. by repeat split;
    first apply map_union_id_l; first apply map_disjoint_empty_l.
Qed.
Theorem principle_of_denial eval γ e Pₒₓ λQₒₓ Pᵤₓ Qᵤₓ ε :
  ux_triple eval γ e Pᵤₓ Qᵤₓ ε →
  ⊨ (Pᵤₓ →ₕ Pₒₓ) →
  ¬ ⊨ (Qᵤₓ →ₕ ∃ₕ v, (⌞ ε = Ok v ⌟ ∗ λQₒₓ v)) →
  ¬ ox_triple eval γ e Pₒₓ λQₒₓ.
Proof.
  intros Hux HPimp HnQimp Hox. apply HnQimp.
  by eapply principle_of_agreement.
Qed.

(* Reasoning principles under type specification contexts *)
Definition valid_src τs vs P := ⊨ (P →ₕ [∗ₜ vs [⊲] boxes τs]).
Definition type_sound Λ := valid_type_ctx (impls Λ) (types Λ).
(* Derivable states must satisfy the output type invariant *)
Theorem principle_of_validity Λ e τ Q ε :
  type_sound Λ → derivable_post Λ (λ s, valid_src) e τ Q ε →
  ⊨ (Q →ₕ (∃ₕ v, (⌞ ε = Ok v ⌟ ∗ [∗ₜ [v ⊲ box τ]]))).
Proof.
  intros HenvT [f [τs [Htype [_ [vs [P [HP [L [Hspec _]]]]]]]]].
  (* Obtain the OX triple *)
  eapply HenvT in Htype as [xs [body [Himpl Hox]]].
  (* Obtain the UX triple *)
  eapply ux_frame_soundness, call_spec in Hspec as Hux; last done.
  (* The goal follows from the principle of agreement *)
  by eapply principle_of_agreement.
Qed.
(* Undefined behaviour is provably reachable *)
Definition ub_derivable Λ :=
  ∃ e τ Q ε, derivable_post Λ (λ s, valid_src) e τ Q ε ∧ sat Q ∧ ¬ ∃ v, ε = Ok v.
(* Type-sound libraries must never exhibit undefined behaviour *)
Theorem type_unsoundness Λ :
  ub_derivable Λ → ¬ type_sound Λ.
Proof.
  intros [?[?[?[?[?[[? Hsat] Hε]]]]]] Hsound.
  eapply principle_of_validity in Hsound; last done.
  apply Hsound in Hsat as [?[?[?[?[?[[_ ?] _]]]]]].
  by apply Hε; eexists.
Qed.
