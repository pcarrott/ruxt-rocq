From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics.
From RUXt.logic Require Export typing.
From RUXt.logic Require Export specs.


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

(* Reasoning principles for type specification contexts *)
Theorem principle_of_validity γ Γ Δ f xs e τs τ vs P Q ε :
  (* Function f exists in context γ with params xs and body e *)
  γ !! f = Some {(xs) e} →
  (* Function f is declared in context Δ with input types τs and output type τ *)
  Δ !! f = Some {τs ↣ τ} →
  (* Derived UX specs Γ are valid wrt implementation context γ *)
  γ ≺ₛ Γ →
  (* Under context Γ, post (ε, Q) is derived from pre (P) by
     replacing occurrences of xs in e with concrete values vs *)
  Γ ⊢ ⌈ P ⌉ e⌊vs[//]xs⌋ ⌈ ε, Q ⌉ → 
  (* Pre (P) implies that values vs are of input type τs *)
  ⊨ (P →ₕ [∗ₜ vs [⊲] boxes τs]) →
  (* Then, assuming that the declared function types Δ
     are valid wrt the function implementations γ, ... *)
  valid_types γ Δ →
  (* ... the derived post (Q) implies that output value v is of type τ
     and executing the call does not terminate in an error *)
  ⊨ (Q →ₕ (∃ₕ v, (⌞ ε = Ok v ⌟ ∗ [∗ₜ [v ⊲ box τ]]))).
Proof.
  intros HFimpl HFtype HenvS Hrule HPtype.
  (* Obtain the UX triple *)
  apply env_soundness in HenvS as Hspecs.
  apply ux_soundness in Hrule as Hux.
  specialize (Hux _ Hspecs) as [].
  (* Assume type validity and obtain the OX triple *)
  intros HenvT. apply HenvT in HFtype as [? [? [HFimpl' Hox]]].
  rewrite HFimpl' in HFimpl; inversion HFimpl; subst.
  (* The goal follows from the principle of agreement *)
  by eapply principle_of_agreement.
Qed.
Theorem principle_of_refutation γ Γ Δ f xs e τs τ vs P Q ε :
  (* Function f exists in context γ with params xs and body e *)
  γ !! f = Some {(xs) e} →
  (* Function f is declared in context Δ with input types τs and output type τ *)
  Δ !! f = Some {τs ↣ τ} →
  (* Derived UX specs Γ are valid wrt implementation context γ *)
  γ ≺ₛ Γ →
  (* Under context Γ, post (ε, Q) is derived from pre (P) by
     replacing occurrences of xs in e with concrete values vs *)
  Γ ⊢ ⌈ P ⌉ e⌊vs[//]xs⌋ ⌈ ε, Q ⌉ → 
  (* Termination is not successful *)
  (¬ ∃ v, ε = Ok v) →
  (* Pre (P) implies that values vs are of input type τs *)
  ⊨ (P →ₕ [∗ₜ vs [⊲] boxes τs]) →
  (* Then, if Q is a satisfiable assertion, ... *)
  sat Q →
  (* ... the declared function types Δ are not valid wrt the function
     implementations γ *)
  ¬ valid_types γ Δ.
Proof.
  intros HFimpl HFtype HenvS Hrule Hε HPtype HQsat Hvalid.
  eapply principle_of_validity in Hvalid; try done. apply HQsat.
  intros h [?[?[?[?[?[[_ ?] _]]]]]]%Hvalid. by apply Hε; eexists.
Qed.
