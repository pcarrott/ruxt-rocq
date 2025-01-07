From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics.
From RUXt.logic Require Export typing.
From RUXt.logic Require Export specs.
From RUXt.logic Require Import sound.


(*** Type refutation via subvariant learning ***)

(* Type summaries for subvariants *)
Record summary := mk_summary { ty : type; ret : val; post : asrt }.
Definition summ_ctx := list summary.

(* Well-formed (precondition) assertions *)
Inductive wf_asrt : summ_ctx → list type → list val → asrt → Prop :=
| A_Emp Σ :
  wf_asrt Σ [] [] EMP
| A_Star Σ τs vs P τ v Q :
  wf_asrt Σ τs vs P → mk_summary τ v Q ∈ Σ →
  wf_asrt Σ (τ :: τs) (v :: vs) (Q ∗ P).
(* Type refutation algorithm *)
Definition try_refute (γ : impl_ctx) (Δ : type_ctx) Σ f vs (σ : option summary) :=
  ∃ τs τ P Q ε,
    (* The function is safely typed *)
    Δ !! f = Some {τs ↣ τ} ∧
    (* P is a valid precondition *)
    wf_asrt Σ τs vs P ∧
    (* [ε: Q] is a derived postcondition *)
    wf_fun_spec γ f vs P Q ε ∧
    match σ with
    | Some σ => τ = ty σ ∧ Q = post σ ∧ ε = Ok (ret σ)
    | None => ¬ ∃ v, ε = Ok v
    end.
(* Well-formed type summary contexts *)
Inductive wf_summ_ctx : impl_ctx → type_ctx → summ_ctx → Prop :=
| L_Nil γ Δ : 
  wf_summ_ctx γ Δ []
| L_Cons γ Δ Σ f vs σ :
  wf_summ_ctx γ Δ Σ → try_refute γ Δ Σ f vs (Some σ) →
  wf_summ_ctx γ Δ (σ :: Σ).

(* Semantic interpretation of well-formed constructs *)
Definition valid_asrt Σ τs vs P :=
  ∃ Σ', Σ' ⊆+ Σ ∧ τs = map ty Σ' ∧ vs = map ret Σ' ∧ P = [∗ map post Σ', id].
Definition valid_summ_ctx γ Δ (Σ : summ_ctx) :=
  valid_types γ Δ → ∀ σ, σ ∈ Σ → ⊨ (post σ →ₕ [∗ₜ [ret σ ⊲ box (ty σ)]]).
(* Soundness *)
Lemma asrt_soundness Σ τs vs P :
  wf_asrt Σ τs vs P → valid_asrt Σ τs vs P.
Proof. Admitted.
Lemma summ_ctx_soundness γ Δ Σ :
  wf_summ_ctx γ Δ Σ → valid_summ_ctx γ Δ Σ.
Proof. Admitted.

(* Adequacy result for refuted types *)
Section Adequacy.
  Context (γ : impl_ctx) (Δ : type_ctx).

  Definition exhibits_ub Σ f vs :=
    ∃ τs τ P Q ε,
      (* The function is safely typed *)
      Δ !! f = Some {τs ↣ τ} ∧
      (* Undefined behaviour is provably reachable *)
      valid_fun_spec γ f vs P Q ε ∧ (¬ ∃ v, ε = Ok v) ∧
      (* The specification is meaningful *)
      valid_asrt Σ τs vs P ∧ sat Q.

  Definition has_unsafe_trace :=
    (* Valid type subvariants may be learned, such that... *)
    ∃ Σ, valid_summ_ctx γ Δ Σ ∧
    (* ... some safe function exhibits undefined behaviour for some input *)
    ∃ f vs, exhibits_ub Σ f vs.

  Theorem adequacy Σ f vs :
    wf_summ_ctx γ Δ Σ → try_refute γ Δ Σ f vs None → has_unsafe_trace.
  Proof. Admitted.
End Adequacy.
