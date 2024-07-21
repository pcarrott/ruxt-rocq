From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics.
From RUXt.logic Require Export specs.
From RUXt.logic Require Export typing.


(*** Properties relating OX and UX reasoning ***)

(* Reasoning principles for triples *)
Theorem principle_of_agreement γ e Pₒₓ Qₒₓ v Pᵤₓ Qᵤₓ ε :
  ux_triple γ e Pᵤₓ Qᵤₓ ε →
  ⊢ (Pᵤₓ ⇒ Pₒₓ) →
  ox_triple γ e Pₒₓ Qₒₓ v →
  ⊢ (Qᵤₓ ⇒ (⌜ ε = Ok v ⌝ ∗ Qₒₓ)).
Proof.
  intros Hux HPimp Hox h' HQux. exists ∅, h'.
  split; first apply map_union_id_left.
  split; first apply map_disjoint_empty_l.
  apply Hux in HQux as [h [HPux [Hstep Hε]]].
  split; by specialize (Hox _ (HPimp h HPux) _ _ Hstep) as [].
Qed.
Theorem principle_of_denial γ e Pₒₓ Qₒₓ v Pᵤₓ Qᵤₓ ε :
  ux_triple γ e Pᵤₓ Qᵤₓ ε →
  ⊢ (Pᵤₓ ⇒ Pₒₓ) →
  ¬ ⊢ (Qᵤₓ ⇒ Qₒₓ) →
  ¬ ox_triple γ e Pₒₓ Qₒₓ v.
Proof.
  intros Hux HPimp HnQimp Hox. apply HnQimp. intros h HQux.
  specialize (principle_of_agreement _ _ _ _ _ _ _ _ Hux HPimp Hox).
  intros HQimp. apply HQimp in HQux as [? [h' [? [? [Hok HQox]]]]].
  inversion Hok; subst. by rewrite <- (map_union_id_left h').
Qed.
Theorem principle_of_error γ e Pₒₓ Qₒₓ v Pᵤₓ Qᵤₓ ξ :
  ux_triple γ e Pᵤₓ Qᵤₓ (Err ξ) →
  ⊢ (Pᵤₓ ⇒ Pₒₓ) →
  ⊢ Qᵤₓ →
  ¬ ox_triple γ e Pₒₓ Qₒₓ v.
Proof.
  intros Hux HPimp HQux Hox.
  specialize (principle_of_agreement _ _ _ _ _ _ _ _ Hux HPimp Hox).
  intros HQimp. eapply HQimp in HQux as [? [h' [? [? [Hok HQox]]]]].
  by inversion Hok. Unshelve. exact ∅.
Qed.

(* Validity of function type specification contexts *)
Theorem type_ctx_validity γ Γ Δ f xs e τs τ vs P Q ε :
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
  ⊢ (P ⇒ [∗ vs [⊲] boxes τs]) →
  (* Then, assuming that the declared function types Δ
     are valid wrt the function implementations γ, ... *)
  valid_types γ Δ →
  (* ... the derived post (Q) implies that output value v is of type τ
     and executing the call does not terminate in an error *)
  ⊢ (Q ⇒ ∃∃ v, (⌜ ε = Ok v ⌝ ∗ [∗ [v ⊲ box τ]])).
Proof.
  intros HFimpl HFtype HenvS Hrule HPtype.
  (* Obtain the UX triple *)
  apply env_soundness in HenvS as Hspecs.
  apply ux_soundness in Hrule as Hux.
  specialize (Hux _ Hspecs).
  (* Assume type validity and obtain the OX triple *)
  intros HenvT. apply HenvT in HFtype as [? [? [HFimpl' Hox]]].
  rewrite HFimpl' in HFimpl; inversion HFimpl; subst.
  specialize (Hox vs) as [v Hox].
  (* The goal follows from the principle of agreement *)
  intros h' HQ. exists v. by eapply principle_of_agreement.
Qed.
