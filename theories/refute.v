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
  wf_input Σ 𝕋 P → mk_summary τ v Q ∈ Σ →
  wf_input Σ (v ⊲ τ :: 𝕋) (Q ∗ P).
(* Type refutation algorithm *)
Record library := mk_library { impls : impl_ctx; types : type_ctx }.
Definition derivable_post Λ Σ τ Q ε :=
  (* Some function f outputs values of type τ *)
  ∃ f τs, types Λ !! f = Some {τs ↣ τ} ∧
  (* vs is a valid input with some valid precondition [P] *)
  ∃ vs P, wf_input Σ (vs [⊲] τs) P ∧ length vs = length τs ∧
  (* [ε: Q] is a valid postcondition from executing f *)
  wf_fun_spec (impls Λ) f vs P Q ε.
Definition try_refute Λ Σ (ς : option summary) :=
  (* Postcondition [ε: Q] is reachable with output type τ *)
  ∃ τ Q ε, derivable_post Λ Σ τ Q ε ∧ sat Q ∧
  (* A new summary for τ is learned iff termination is successful *)
  ς = match ε with Ok v => Some (mk_summary τ v Q) | _ => None end.
(* Well-formed type summary contexts *)
Inductive wf_summ_ctx : library → summ_ctx → Prop :=
| L_Nil Λ : 
  wf_summ_ctx Λ []
| L_Cons Λ Σ ς :
  wf_summ_ctx Λ Σ → try_refute Λ Σ (Some ς) →
  wf_summ_ctx Λ (ς :: Σ).

(* Semantic interpretation of valid inputs *)
Definition valid_input Σ 𝕋 P :=
  ∃ Σ', Σ' ⊆ Σ ∧ P = [∗ map post Σ', id] ∧ 𝕋 = map ret Σ' [⊲] map ty Σ'.
(* Soundness *)
Lemma input_soundness Σ 𝕋 P :
  wf_input Σ 𝕋 P → valid_input Σ 𝕋 P.
Proof.
  intros Hinput. induction Hinput.
  + exists []. by split; first apply list_subseteq_nil.
  + destruct IHHinput as [Σ' [Hsub [-> ->]]].
    set (ς := {| ty := τ; ret := v; post := Q |}).
    exists (ς :: Σ'). split; last done. by apply list_subseteq_cons_iff.
Qed.

(* A program constructed solely from [safe] calls to the library *)
Fixpoint only_safe_calls (Δ : type_ctx) (Σ : summ_ctx) (e : expr) :=
  match e with
  | Let _ e1 e2 | Choice e1 e2 => only_safe_calls Δ Σ e1 ∧ only_safe_calls Δ Σ e2
  | Call f ts => ∃ vs, ts = TVals vs ∧ ∃ τs τ, Δ !! f = Some {τs ↣ τ} ∧
                 ∃ Σ', Σ' ⊆ Σ ∧ vs = map ret Σ' ∧ τs = map ty Σ'
  | Pure _ | Assume _ | Alloc _ => True
  | _ => False
  end.
(* Properties *)
Lemma only_safe_calls_subseteq Δ Σ Σ' e :
  only_safe_calls Δ Σ' e → Σ' ⊆ Σ → only_safe_calls Δ Σ e.
Proof.
  intros Hsafe Hsub. induction e; try done.
  + destruct Hsafe as []. split.
    - by apply IHe1.
    - by apply IHe2.
  + destruct Hsafe as []. split.
    - by apply IHe1.
    - by apply IHe2.
  + destruct Hsafe as [? [-> [? [? [Htype [Σ'' [Hsub' [-> ->]]]]]]]].
    eexists; split; first done. do 2 eexists; split; first done.
    exists Σ''. by split; first etrans.
Qed.

(* A [main] function starts from [EMP] and only has [safe] calls to the library *)
Definition reachable_from_main Λ Σ (Q : asrt) (ε : exit) :=
  ∃ e, only_safe_calls (types Λ) Σ e ∧ ∃ Γ, (impls Λ) ≺ₛ Γ ∧ Γ ⊢ ⌈ EMP ⌉ e ⌈ ε , Q ⌉.
(* Properties *)
Lemma reachable_from_main_subseteq Λ Σ Σ' Q ε :
  reachable_from_main Λ Σ' Q ε → Σ' ⊆ Σ → reachable_from_main Λ Σ Q ε.
Proof.
  intros [e [Hsafe Hreach]] Hsub.
  by eexists; split; first eapply only_safe_calls_subseteq.
Qed.

(* Semantic interpretation of valid summaries *)
Definition valid_summ_ctx Λ Σ :=
  ∀ ς, ς ∈ Σ → reachable_from_main Λ Σ (post ς) (Ok (ret ς)).
(* Properties *)
Lemma subseteq_reachable Λ Σ Σ' :
  valid_summ_ctx Λ Σ → Σ' ⊆ Σ →
  ∃ v, reachable_from_main Λ Σ ([∗map post Σ', id]) (Ok v).
Proof.
  intros Hsumm Hsub. induction Σ'.
  + simpl. exists VUnit, (Pure (PVal VUnit)).
    split; first done.
    eexists. split; last eapply S_Value.
    apply wf_empty_spec_ctx.
  + simpl. unfold valid_summ_ctx in Hsumm.
    eapply list_subseteq_cons_iff in Hsub as [Hin Hsub].
    apply Hsumm in Hin as [e [Hsafe [Γ [Henv Hspec]]]].
    apply IHΣ' in Hsub as [v [e' [Hsafe' [Γ' [Henv' Hspec']]]]].
    exists v, (Let <> e e'); split; first done.
    exists (Γ [∪] Γ'); split; first by apply E_Union.
    eapply S_Let; first by apply S_EnvUnion.
    simpl. rewrite spec_ctx_union_comm. apply S_EnvUnion.
    by apply S_CommPost, S_FrameEmpL, S_CommPre, S_Frame.
Qed.
Lemma derivable_from_main Λ Σ τ Q ε :
  valid_summ_ctx Λ Σ → derivable_post Λ Σ τ Q ε →
  reachable_from_main Λ Σ Q ε.
Proof.
  intros Hsumm [f [τs [Htype [vs [P [Hinput [Hlen Hfun]]]]]]].
  apply input_soundness in Hinput as [Σ'' [Hsub' [-> H𝕋]]].
  specialize (subseteq_reachable _ _ _ Hsumm Hsub') as [? Hreach].
  destruct Hreach as [e [Hsafe [Γ [Henv Hspec]]]].
  exists (Let <> e (Call f (TVals vs))). split.
  + split; first by eapply only_safe_calls_subseteq.
    eexists; split; first done. do 2 eexists; split; first done.
    exists Σ''. split; first by etrans.
    apply (zip_with_inj TyOwn); try done; solve_length.
  + destruct Hfun as [Γs [s [HSome [Hs]]]].
    exists (Γ [∪] Γs). split; first by apply E_Union.
    eapply S_Let; first by apply S_EnvUnion.
    rewrite spec_ctx_union_comm. apply S_EnvUnion.
    by eapply S_Call.
Qed.
(* Soundness *)
Lemma summ_ctx_soundness Λ Σ :
  wf_summ_ctx Λ Σ → valid_summ_ctx Λ Σ.
Proof.
  intros Hsumm. induction Hsumm.
  + inversion 1.
  + intros ς' Hin. apply elem_of_cons in Hin as [<-|Hin].
    - destruct H as [τ [Q [ε [Hpost [Hsat Hε]]]]].
      destruct ε; try done. inversion Hε; subst; clear Hε.
      eapply derivable_from_main in IHHsumm as Hreach; last done.
      by eapply reachable_from_main_subseteq; last apply list_subseteq_cons.
    - apply IHHsumm in Hin as Hreach.
      by eapply reachable_from_main_subseteq; last apply list_subseteq_cons.
Qed.

(* A type assignment can be refuted *)
Definition has_refuted_type Λ :=
  ∃ Σ, wf_summ_ctx Λ Σ ∧ try_refute Λ Σ None.
(* A [main] program exhibits undefined behaviour *)
Definition ub_reachable Λ :=
  ∃ Σ, valid_summ_ctx Λ Σ ∧ ∃ Q ε, reachable_from_main Λ Σ Q ε ∧ sat Q ∧ ¬ ∃ v, ε = Ok v.
(* Adequacy result for refuted type assignments *)
Theorem inadequate Λ :
  has_refuted_type Λ → ub_reachable Λ.
Proof.
  intros [Σ [Hctx%summ_ctx_soundness [τ [Q [ε [Hpost [Hsat Hε]]]]]]].
  eexists; split; first done. do 2 eexists; split; first by eapply derivable_from_main.
  by split; last by intros [? ->].
Qed.
