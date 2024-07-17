From RUXt.lang Require Import semantics.
From RUXt.logic Require Export specs.
From RUXt.logic Require Export typing.


(*** Properties relating OX and UX reasoning ***)

(* Reasoning principles for triples *)
Theorem principle_of_agreement γ e Pₒₓ Qₒₓ v Pᵤₓ Qᵤₓ ε :
  ux_triple γ e Pᵤₓ Qᵤₓ ε →
  (⊢ (Pᵤₓ ⇒ Pₒₓ)) →
  ox_triple γ e Pₒₓ Qₒₓ v →
  (⊢ (Qᵤₓ ⇒ Qₒₓ)) ∧ (Qᵤₓ ⊢ ⌜ ε = Ok v ⌝).
Proof.
  intros Hux HPimp Hox. split.
  + intros h' HQux. apply Hux in HQux as [h [HPux [Hstep Hε]]].
    by specialize (Hox _ (HPimp h HPux) _ _ Hstep) as [HQox _].
  + intros h' HQux. apply Hux in HQux as [h [HPux [Hstep Hε]]].
    specialize (Hox _ (HPimp h HPux) _ _ Hstep) as [HQox Hexit].
    eexists. split; first done. apply map_empty_subseteq.
Qed.
Theorem principle_of_denial γ e Pₒₓ Qₒₓ v Pᵤₓ Qᵤₓ ε :
  ux_triple γ e Pᵤₓ Qᵤₓ ε →
  (⊢ (Pᵤₓ ⇒ Pₒₓ)) →
  ¬ (⊢ (Qᵤₓ ⇒ Qₒₓ)) →
  ¬ ox_triple γ e Pₒₓ Qₒₓ v.
Proof.
  intros Hux HPimp HQux Hox. apply HQux. 
  specialize (principle_of_agreement _ _ _ _ _ _ _ _ Hux HPimp Hox).
  by intros [HQimp _].
Qed.
Theorem principle_of_error γ e Pₒₓ Qₒₓ v Pᵤₓ Qᵤₓ ξ :
  ux_triple γ e Pᵤₓ Qᵤₓ (Err ξ) →
  (⊢ (Pᵤₓ ⇒ Pₒₓ)) →
  (⊢ Qᵤₓ) →
  ¬ ox_triple γ e Pₒₓ Qₒₓ v.
Proof.
  intros Hux HPimp HQux Hox. simpl in *.
  specialize (principle_of_agreement _ _ _ _ _ _ _ _ Hux HPimp Hox).
  intros [_ Hfalse]. specialize (Hfalse ∅ (HQux ∅)).
  by inversion Hfalse as [? [[]]].
Qed.
