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

(* An interpretation context maps type identifiers to their semantic interpretation *)
Definition interp_ctx := gmap tid type.
Global Instance type_inhabited : Inhabited type := populate unit.
Definition to_type (𝕀 : interp_ctx) (τ : tid) : type := 𝕀 !!! τ.
Notation to_types 𝕀 τs := (to_type 𝕀 <$> τs).
Definition insert_fun_type 𝕀 f s (Δ : type_ctx) :=
  match s with {τs ↣ₛ τ} => <[f := {to_types 𝕀 τs ↣ to_type 𝕀 τ}]>Δ end.
Definition to_type_ctx (Δ : sign_ctx) (𝕀 : interp_ctx) : type_ctx :=
  map_fold (insert_fun_type 𝕀) ∅ Δ.
(* Properties *)
Lemma lookup_type_sign_Some Δ 𝕀 f τs τ :
  Δ !! f = Some {τs ↣ₛ τ} →
  to_type_ctx Δ 𝕀 !! f = Some {to_types 𝕀 τs ↣ to_type 𝕀 τ}.
Proof.
  induction Δ using map_ind; intros Htype.
  + by apply lookup_empty_Some in Htype.
  + unfold to_type_ctx. destruct x as [τs' τ'].
    rewrite (map_fold_insert_L _ _ _ _ m).
    - destruct (decide (i = f)) as [->|].
      * rewrite (lookup_insert m) in Htype.
        inversion Htype; subst.
        eapply lookup_insert.
      * rewrite (lookup_insert_ne m) in Htype; last done.
        rewrite <- IHΔ; last done.
        by eapply lookup_insert_ne.
    - intros ? ? [] [] ? Hneq _ _. by apply insert_commute.
    - done.
Qed.

(* A safe context constitutes a valid type subvariant *)
Definition is_subvariant 𝕀 τs vs P (_ : list expr) :=
  ⊨ (P →ₕ [∗ₜ vs [⊲] boxes (to_types 𝕀 τs)]).
(* A library Λ is type-sound wrt the semantic interpretation of 𝕀 *)
Definition type_sound Λ 𝕀 := valid_type_ctx (impls Λ) (to_type_ctx (types Λ) 𝕀).
(* Derivable states must satisfy the output type invariant *)
Theorem principle_of_validity Λ 𝕀 e τ Q ε :
  type_sound Λ 𝕀 → derivable_post (is_subvariant 𝕀) Λ τ ε Q e →
  ⊨ (Q →ₕ (∃ₕ v, (⌞ ε = Ok v ⌟ ∗ [∗ₜ [v ⊲ box (to_type 𝕀 τ)]]))).
Proof.
  intros Hsound [f [τs [Htype [vs [P [es [Hsubv [L [Hspec _]]]]]]]]].
  (* Obtain the OX triple *)
  eapply lookup_type_sign_Some, Hsound in Htype as [xs [body [Himpl Hox]]].
  (* Obtain the UX triple *) 
  eapply ux_frame_soundness, call_spec in Hspec as Hux; last done.
  (* The goal follows from the principle of agreement *)
  by eapply principle_of_agreement.
Qed.

(* Undefined behaviour is provably reachable *)
Definition ub_derivable Λ 𝕀 :=
  ∃ e τ Q ε, derivable_post (is_subvariant 𝕀) Λ τ ε Q e ∧ sat Q ∧ ¬ ∃ v, ε = Ok v.
(* Type-sound libraries must never exhibit undefined behaviour *)
Theorem type_unsoundness Λ 𝕀 :
  ub_derivable Λ 𝕀 → ¬ type_sound Λ 𝕀.
Proof.
  intros [?[?[?[?[?[[? Hsat] Hε]]]]]] Hsound.
  eapply principle_of_validity in Hsound; last done.
  apply Hsound in Hsat as [?[?[?[?[?[[_ ?] _]]]]]].
  by apply Hε; eexists.
Qed.
