From RUXt.lang Require Import semantics.
From RUXt.model Require Export logic summary.


(*** The Type Refutation Algorithm ***)

(* Libraries *)
Record library := mk_library { impls : impl_ctx; types : sign_ctx }.

(* Bindings *)
Definition bindings xs es e :=
  foldr (λ xe e, Let (BNamed xe.1) xe.2 e) e (zip xs es).
(* Well-typed states that can be derived by some UX logic *)
Definition derivable_post is_safe Λ τ ε Q e :=
  (* Some function f outputs values of type τ *)
  ∃ f τs, types Λ !! f = Some {τs ↣ₛ τ} ∧
  (* Programs es generate values vs and precondition [P] *)
  ∃ vs P es, is_safe τs vs P es ∧
  (* [ε:Q] is a postcondition obtained from executing f *)
  ∃ L, (derivable_spec L) (impls Λ) (Call f (TVals vs)) P Q ε ∧
  (* e is a witness program that calls f on the values returned by es *)
  ∃ xs, e = bindings xs es (Call f (TVars xs)) ∧ length xs = length es ∧ NoDup xs.

(* Safe contexts *)
Inductive wf_context : summ_ctx → list tid → list val → asrt → list expr → Prop :=
| I_Emp Σ :
  wf_context Σ [] [] EMP []
| I_Star Σ τs vs P es τ v Q e :
  wf_context Σ τs vs P es → mk_summary v Q e ∈ Σ !!! τ →
  wf_context Σ (τ :: τs) (v :: vs) (Q ∗ P) (e :: es).
Definition safe_context Σ τs vs P es := wf_context Σ τs vs P es.
(* The refutation procedure *)
Definition try_refute Λ Σ (Σ' : summ_ctx + expr) :=
  (* Postcondition [ε: Q] is reachable with output type τ *)
  ∃ τ ε Q e, derivable_post (safe_context Σ) Λ τ ε Q e ∧ sat Q ∧
  (* A new summary for τ is learned iff termination is successful *)
  Σ' = match ε with Ok v => inl (update (mk_summary v Q e) τ Σ) | _ => inr e end.
(* Well-formed type summary contexts *)
Inductive wf_summ_ctx : library → summ_ctx → Prop :=
| R_Nil Λ : 
  wf_summ_ctx Λ ∅
| R_Cons Λ Σ Σ' :
  wf_summ_ctx Λ Σ → try_refute Λ Σ (inl Σ') →
  wf_summ_ctx Λ Σ'.

(* Semantic interpretation of valid contexts *)
Definition valid_context (Σ : summ_ctx) τs vs P es :=  
  ∃ Σ', Σ' ⊆ flat_summ_ctx Σ ∧
    τs = Σ'.*1 ∧
    vs = ret <$> Σ'.*2 ∧
    P = [∗ post <$> Σ'.*2, id] ∧
    es = src <$> Σ'.*2.
(* Soundness *)
Theorem context_soundness Σ τs vs P es :
  wf_context Σ τs vs P es → valid_context Σ τs vs P es.
Proof.
  intros Hinput. induction Hinput.
  + exists []. by split; first apply list_subseteq_nil.
  + destruct IHHinput as [Σ' [Hsub [-> [-> [-> ->]]]]].
    set (ς := {| ret := v; post := Q ; src := e|}).
    exists ((τ, ς) :: Σ'). split; last done.
    apply list_subseteq_cons_iff.
    by split; first apply elem_of_flat.
Qed.

(* Summaries are reachable from some [main] program *)
Definition reachable_from_program 𝕍 xs vs P Λ τ ε Q e := 
  safe_program 𝕍 (types Λ) e = Some τ ∧
  ux_frame_triple (impls Λ) (e⌊vs [//] xs⌋) P Q ε.
Notation reachable_from_main := (reachable_from_program ∅ [] [] EMP).
(* Semantic interpretation of valid summaries *)
Definition valid_summ_ctx Λ (Σ : summ_ctx) :=
  ∀ τ ς, ς ∈ Σ !!! τ → reachable_from_main Λ τ (Ok (ret ς)) (post ς) (src ς).
(* Properties *)
Lemma reachable_bindings Λ Σ Σ1 Σ2 xs1 xs2 τ ε Q e :
  valid_summ_ctx Λ Σ → Σ1 ++ Σ2 ⊆ flat_summ_ctx Σ →
  NoDup (xs1 ++ xs2) → length xs1 = length Σ1 → length xs2 = length Σ2 →
  reachable_from_program
    (cons_var_ctx (xs1 ++ xs2) (Σ1 ++ Σ2).*1) (xs1 ++ xs2) (ret <$> (Σ1 ++ Σ2).*2)
    ([∗ post <$> (Σ1 ++ Σ2).*2, id]) Λ τ ε Q e →
  reachable_from_program
    (cons_var_ctx xs1 Σ1.*1) xs1 (ret <$> Σ1.*2)
    ([∗ post <$> Σ1.*2, id]) Λ τ ε Q (bindings xs2 (src <$> Σ2.*2) e).
Proof.
  intros Hsumm Hsub Hdup Hlen1 Hlen2 Hreach; subst.
  rewrite reverse_var_ctx; last first.
  { by apply NoDup_app in Hdup as []. }
  { by rewrite length_fmap. }
  rewrite reverse_var_ctx in Hreach; last first.
  { done. }
  { rewrite length_fmap, 2 length_app; lia. }
  generalize dependent e; generalize dependent Σ1;
    generalize dependent xs2; generalize dependent xs1.
  induction Σ2 as [|ς Σ2]; simpl in *; intros xs1 xs2 Hdup Hlen2 Σ1 Hsub Hlen1 e Hreach.
  + apply nil_length_inv in Hlen2; simpl in *; subst.
    rewrite 2 (right_id_L _ (++)) in *.
    by unfold bindings; simpl.
  + destruct xs2 as [|x xs2]; first done. inversion Hlen2 as [Hlen2'].
    assert (x ∉ xs1 ∧ x ∉ xs2) as [Hnin1 Hnin2].
    {
      subst; apply NoDup_app in Hdup as [_ [Hnin []%NoDup_cons]].
      by split; first (intros Hin%Hnin; apply Hin; left).
    }
    rewrite cons_middle, app_assoc in Hdup.
    rewrite cons_middle, app_assoc in Hsub. 
    rewrite 2 cons_middle, 2 app_assoc in Hreach. 
    assert (length (xs1 ++ [x]) = length (Σ1 ++ [ς]))
      as Hlen1' by by rewrite 2 length_app; simpl; lia.
    specialize (IHΣ2 _ _ Hdup Hlen2' _ Hsub Hlen1' _ Hreach) as [Hsafe Hux].
    assert (ς.2 ∈ Σ !!! ς.1) as [Hsafe' Hux']%Hsumm.
    {
      eapply elem_of_flat, elem_of_subseteq; last done.
      apply elem_of_app; left. apply elem_of_app; right.
      by destruct ς; left.
    }
    split; simpl.
    - eapply safe_main_Some in Hsafe' as ->.
      rewrite insert_var_ctx; last by rewrite 2 length_reverse; solve_length.
      by rewrite <- 2 reverse_snoc, <- list_fmap_singleton, <- fmap_app.
    - unfold bindings; simpl.
      apply safe_main_closed in Hsafe'.
      rewrite let_subst; try done; last solve_length.
      eapply (let_spec _ _ _ _ _ _ ([∗post <$> Σ1.*2 ++ [ς.2], id])).
      * by rewrite fmap_app; apply frame_app_spec.
      * rewrite subst_vals_subst; last solve_length.
        by rewrite <- 2 list_fmap_singleton, <- 2 fmap_app.
Qed.
Lemma derivable_for_main Λ Σ e τ Q ε :
  valid_summ_ctx Λ Σ → derivable_post (safe_context Σ) Λ τ ε Q e →
  reachable_from_main Λ τ ε Q e.
Proof.
  intros Hsumm [f [τs [Htype [vs [P [es [Hctx [L [Hspec [xs [-> [Hlen Hdup]]]]]]]]]]]].
  apply context_soundness in Hctx as [Σ' [Hsub [-> [-> [-> ->]]]]].
  apply ux_frame_soundness in Hspec.
  specialize (reachable_bindings Λ Σ [] Σ' [] xs τ ε Q (Call f (TVars xs))) as Hbindings.
  assert (length xs = length Σ') as Hlen' by solve_length.
  specialize (Hbindings Hsumm Hsub Hdup eq_refl Hlen').
  apply Hbindings. split.
  + by apply safe_call; first solve_length.
  + rewrite subst_call_args; try done; solve_length.
Qed.
(* Soundness *)
Theorem summ_ctx_soundness Λ Σ :
  wf_summ_ctx Λ Σ → valid_summ_ctx Λ Σ.
Proof.
  intros Hsumm. induction Hsumm as [|? ? ? ? ? Hrefute].
  + inversion 1.
  + intros τ' ς' Hin.
    destruct Hrefute as [τ [ε [Q [e [Hpost [Hsat Hε]]]]]].
    destruct ε; try done. inversion Hε; subst; clear Hε.
    destruct (decide (τ = τ')) as [<-|].
    - rewrite lookup_total_update in Hin.
      apply elem_of_cons in Hin as [->|]; last by eapply IHHsumm.
      by eapply derivable_for_main.
    - by rewrite lookup_total_update_ne in Hin; first eapply IHHsumm.
Qed.

(* A type assignment in the library can be refuted *)
Definition has_refuted_type Λ e :=
  ∃ Σ, wf_summ_ctx Λ Σ ∧ try_refute Λ Σ (inr e).
(* A [main] program exhibits undefined behaviour *)
Definition inadequate Λ e :=
  ∃ h, (impls Λ) ⊢ ⟨ ∅ | e ⟩ ⇓ ⟨ h | Err ⟩ ∧ ∃ τ, safe_main (types Λ) e = Some τ.
(* Adequacy result for refuted type assignments *)
Theorem inadequacy Λ e :
  has_refuted_type Λ e → inadequate Λ e.
Proof.
  intros [Σ [Hctx%summ_ctx_soundness [τ [ε [Q [s [Hpost [Hsat Hε]]]]]]]].
  eapply derivable_for_main in Hpost as [? Hux%ux_triple_preservation]; last done.
  destruct Hsat as [?[?[->]]%Hux].
  destruct ε; inversion Hε; by eexists; split; last eexists.
Qed.
