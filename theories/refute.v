From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics.
From RUXt.logic Require Export typing.
From RUXt.logic Require Export specs.


(*** Type refutation via subvariant learning ***)

(* Summaries for type subvariants *)
Record summary := mk_summary { ty : type; ret : val; post : asrt }.
Definition summ_ctx := list summary.

(* Well-formed input values and preconditions *)
Inductive wf_input : summ_ctx → list typing → asrt → Prop :=
| A_Emp Σ :
  wf_input Σ [] EMP
| A_Star Σ 𝕋 P τ v Q :
  wf_input Σ 𝕋 P →
  mk_summary τ v Q ∈ Σ → v ⊲ τ ∉ 𝕋 →
  wf_input Σ (v ⊲ τ :: 𝕋) (Q ∗ P).
(* Type refutation algorithm *)
Definition try_refute (γ : impl_ctx) (Δ : type_ctx) Σ f vs (ς : option summary) :=
  ∃ τs τ P Q ε,
    (* The function f is safely typed *)
    Δ !! f = Some {τs ↣ τ} ∧
    (* vs is a valid input and [P] is a valid precondition *)
    wf_input Σ (vs [⊲] τs) P ∧
    (* [ε: Q] is a valid postcondition *)
    wf_fun_spec γ f vs P Q ε ∧ sat Q ∧
    (* A new summary is learned iff termination is successful *)
    ς = match ε with Ok v => Some (mk_summary τ v Q) | _ => None end.
(* Well-formed type summary contexts *)
Inductive wf_summ_ctx : impl_ctx → type_ctx → summ_ctx → Prop :=
| L_Nil γ Δ : 
  wf_summ_ctx γ Δ []
| L_Cons γ Δ Σ f vs σ :
  wf_summ_ctx γ Δ Σ → try_refute γ Δ Σ f vs (Some σ) →
  wf_summ_ctx γ Δ (σ :: Σ).

(* Semantic interpretation of well-formed constructs *)
Definition valid_input Σ 𝕋 P :=
  ∃ Σ', Σ' ⊆+ Σ ∧ 𝕋 = map ret Σ' [⊲] map ty Σ' ∧ P = [∗ map post Σ', id].
Definition valid_summary γ (Δ : type_ctx) Σ σ :=
  (* Some function returns the type of the learned summary *)
  ∃ f τs, Δ !! f = Some {τs ↣ ty σ} ∧
  (* The summary is obtained from executing the function on some valid input *)
  ∃ vs P, valid_fun_spec γ f vs P (post σ) (Ok (ret σ)) ∧ valid_input Σ (vs [⊲] τs) P.
Definition valid_summ_ctx γ Δ Σ :=
  ∀ σ, σ ∈ Σ → valid_summary γ Δ Σ σ.
(* Soundness *)
Lemma input_soundness Σ 𝕋 P :
  wf_input Σ 𝕋 P → valid_input Σ 𝕋 P.
Proof.
  intros Hinput. induction Hinput.
  + exists []. by split; first apply submseteq_nil_l.
  + destruct IHHinput as [Σ' [Hsub [-> ->]]].
    set (σ := {| ty := τ; ret := v; post := Q |}).
    exists (σ :: Σ'). split; last done. apply submseteq_cons_l.
    apply elem_of_Permutation in H as []. rewrite H in Hsub.
    eexists. split; first done.
    apply submseteq_cons_r in Hsub as [|[?[]]]; first done.
    assert (σ ∈ Σ'). { apply elem_of_Permutation. by eexists. }
    exfalso. apply H0. clear -H3.
    induction Σ'; first inversion H3.
    simpl. apply elem_of_cons.
    apply elem_of_cons in H3 as [<-|].
    - by left.
    - right. by apply IHΣ'.
Qed.
Lemma valid_input_cons Σ 𝕋 P σ :
  valid_input Σ 𝕋 P →
  valid_input (σ :: Σ) 𝕋 P.
Proof.
  intros [Σ' [Hsub [-> ->]]]. exists Σ'. split; last done.
  apply submseteq_cons_r. by left.
Qed.
Lemma summ_ctx_soundness γ Δ Σ :
  wf_summ_ctx γ Δ Σ → valid_summ_ctx γ Δ Σ.
Proof.
  intros Hsumm. induction Hsumm.
  + inversion 1.
  + intros σ' Hin. apply elem_of_cons in Hin as [<-|Hin].
    - destruct H as [τs [τ [P [Q [ε [?[?[?[]]]]]]]]].
      destruct ε; try done. inversion H3; subst.
      do 2 eexists. split; first done.
      do 2 eexists. split.
      * by apply fun_spec_soundness.
      * by apply valid_input_cons, input_soundness.
    - apply IHHsumm in Hin as [?[?[?[?[?[]]]]]].
      do 2 eexists. split; first done.
      do 2 eexists. split; first done.
      by apply valid_input_cons.
Qed.

(* A type assignment can be refuted *)
Definition has_refuted_type γ Δ :=
  ∃ Σ, wf_summ_ctx γ Δ Σ ∧ ∃ f vs, try_refute γ Δ Σ f vs None.
(* A program constructed solely from [safe] calls to the library *)
Fixpoint only_safe_calls (Δ : type_ctx) (e : expr) :=
  match e with
  | Let _ e1 e2 | Choice e1 e2 => only_safe_calls Δ e1 ∧ only_safe_calls Δ e2
  | Call f _ => f ∈ dom Δ
  | Pure _ | Assume _ | Alloc _ => True
  | _ => False
  end.
(* A [main] program exhibits undefined behaviour *)
Definition exhibits_ub (γ : impl_ctx) (e : expr) :=
  ∃ Q ε, ux_triple γ e EMP Q ε ∧ sat Q ∧ ¬ ∃ v, ε = Ok v.
(* Adequacy result for refuted type assignments *)
Theorem inadequate γ Δ :
  has_refuted_type γ Δ → ∃ e, only_safe_calls Δ e ∧ exhibits_ub γ e.
Proof.
Admitted.
