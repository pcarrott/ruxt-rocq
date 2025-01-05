From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics.
From RUXt.logic Require Export typing.
From RUXt.logic Require Export specs.


(*** Learned type subvariants ***)

(* Function output summaries *)
Record summary := mk_summary { ty : type; ret : val; post : asrt }.
Definition summ_ctx := list summary.

(* Well-formed (precondition) assertions *)
Inductive wf_asrt : summ_ctx → list type → list val → asrt → Prop :=
| A_Emp Σ :
  wf_asrt Σ [] [] EMP
| A_Star Σ τs vs P τ v Q :
  wf_asrt Σ τs vs P → mk_summary τ v Q ∈ Σ →
  wf_asrt Σ (τ :: τs) (v :: vs) (P ∗ Q).
Definition valid_asrt (Σ : summ_ctx) τs vs P :=
  (* TODO *)
  ⊨ (P →ₕ [∗ₜ vs [⊲] boxes τs]).
Lemma asrt_soundness Σ τs vs P :
  wf_asrt Σ τs vs P → valid_asrt Σ τs vs P.
Proof. Admitted.


(*** Type refutation ***)

Definition derivable_spec (γ : impl_ctx) f vs P Q ε :=
  ∃ xs e Γ s,
    (* The function exists in the context *)
    γ !! f = Some {(xs) e} ∧
    (* The spec exists in some derived environment *)
    γ ≺ₛ Γ ∧ Γ !! f = Some s ∧ ⌈(vs) P | ε, Q⌉ ∈ s.
Definition valid_spec (γ : impl_ctx) f vs P Q ε :=
  ∃ xs e Γ s,
    (* The function exists in the context *)
    γ !! f = Some {(xs) e} ∧
    (* The spec exists in some semantically valid environment *)
    valid_spec_ctx γ Γ ∧ Γ !! f = Some s ∧ ⌈(vs) P | ε, Q⌉ ∈ s.
Lemma spec_soundness γ f vs P Q ε :
  derivable_spec γ f vs P Q ε → valid_spec γ f vs P Q ε.
Proof.
  intros [xs [e [Γ [s [Himpl [HenvS [HΓsome Hspec]]]]]]].
  exists xs, e, Γ, s. repeat split; try done.
  by eapply env_soundness.
Qed.

Section Refutation.
  (* We assume that a fixed implementation context exists with safely typed functions *)
  Context {γ : impl_ctx} {Δ : type_ctx}.

  (* The algorithm *)
  Definition try_refute Σ f vs (σ : option summary) :=
    ∃ τs τ P Q ε,
      (* The function is safely typed *)
      Δ !! f = Some {τs ↣ τ} ∧
      (* P is a valid precondition *)
      wf_asrt Σ τs vs P ∧
      (* Q is a derived postcondition *)
      derivable_spec γ f vs P Q ε ∧
      match σ with
      | Some σ => τ = ty σ ∧ Q = post σ ∧ ε = Ok (ret σ)
      | None => ¬ ∃ v, ε = Ok v
      end.

  (* Well-formed type summary contexts *)
  Inductive wf_summ_ctx : summ_ctx → Prop :=
  | C_Nil : 
    wf_summ_ctx []
  | C_Cons Σ f vs σ :
    wf_summ_ctx Σ → try_refute Σ f vs (Some σ) →
    wf_summ_ctx (σ :: Σ).
  Definition valid_summ_ctx (Σ : summ_ctx) :=
    (* TODO *)
    True.
  Lemma summ_ctx_soundness Σ :
    wf_summ_ctx Σ → valid_summ_ctx Σ.
  Proof. Admitted.

  Definition exhibits_ub Σ f vs :=
    ∃ τs τ P Q ε,
      (* The function is safely typed *)
      Δ !! f = Some {τs ↣ τ} →
      (* Undefined behaviour is provably reachable *)
      valid_spec γ f vs P Q ε → (¬ ∃ v, ε = Ok v) →
      (* The specification is meaningful *)
      valid_asrt Σ τs vs P ∧ sat Q.

  Definition has_unsafe_trace :=
    (* Valid type subvariants may be learned, such that... *)
    ∃ Σ, valid_summ_ctx Σ ∧
    (* ... some safe function exhibits undefined behaviour for some input *)
    ∃ f vs, exhibits_ub Σ f vs.

  Theorem adequacy Σ f vs :
    wf_summ_ctx Σ → try_refute Σ f vs None → has_unsafe_trace.
  Proof. Admitted.
End Refutation.
