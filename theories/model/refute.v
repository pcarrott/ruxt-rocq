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
Definition valid_type v τ :=
  match τ with TyBase k => val_type v = k | TyCustom _ => True end.
Inductive wf_context : summ_ctx → list tid → list val → asrt → list expr → Prop :=
| I_Emp Σ :
  wf_context Σ [] [] EMP []
| I_Star Σ τs vs P es τ v ς :
  wf_context Σ τs vs P es →
  ς ∈ Σ !!! τ → valid_type v τ → sat (post (ς v) ∗ P) →
  wf_context Σ (τ :: τs) (v :: vs) (post (ς v) ∗ P) (src (ς v) :: es).
Definition safe_context Σ τs vs P es := wf_context Σ τs vs P es.
(* The refutation procedure *)
Definition try_refute Λ Σ (Σ' : summ_ctx + expr) :=
  match Σ' with
  (* The summary context Σ is updated to Σ' *)
  | inl Σ' =>
      (* A new summary λQ is learned for τ with witness e *)
      ∃ τ λQ λe, Σ' = update (λ v, mk_summary (λQ v) (λe v)) τ Σ ∧
      (* λQ is a satisfiable post for some value v *)
      sat_post λQ ∧
      (* Every v is a reachable safe value (FALSE is vacuously reachable) *)
      ∀ v, derivable_post (safe_context Σ) Λ τ (Ok v) (λQ v) (λe v)
  (* Found witness e for type unsoundness *)
  | inr e =>
      (* Unsuccessful termination is derivable with a satisfiable post *)
      ∃ τ ε Q, derivable_post (safe_context Σ) Λ τ ε Q e ∧ sat Q ∧ ¬ ∃ v, ε = Ok v
  end.
(* Well-formed type summary contexts *)
Inductive wf_summ_ctx : library → summ_ctx → Prop :=
| R_Nil Λ : 
  wf_summ_ctx Λ base_summ_ctx
| R_Cons Λ Σ Σ' :
  wf_summ_ctx Λ Σ → try_refute Λ Σ (inl Σ') →
  wf_summ_ctx Λ Σ'.

(* Semantic interpretation of valid contexts *)
Notation zip_expr Σ vs := (src <$> zip_with (λ v λe, λe v) vs Σ.*2).
Notation zip_asrt Σ vs := ([∗ post <$> zip_with (λ v λe, λe v) vs Σ.*2, id]).
Notation valid_types Σ vs := (Forall2 valid_type vs Σ.*1).
(* A context is valid if it is well-formed and the types are valid *)
Definition valid_context (Σ : summ_ctx) τs vs P es :=  
  ∃ Σ', Σ' ⊆ flat_summ_ctx Σ ∧
    τs = Σ'.*1 ∧ es = zip_expr Σ' vs ∧ P = zip_asrt Σ' vs ∧
    sat P ∧ length vs = length Σ' ∧ valid_types Σ' vs.
(* Soundness *)
Theorem context_soundness Σ τs vs P es :
  wf_context Σ τs vs P es → valid_context Σ τs vs P es.
Proof.
  intros Hinput. induction Hinput.
  + exists []. repeat split; try done.
    - apply list_subseteq_nil.
    - by eexists.
  + destruct IHHinput as [Σ' [Hsub [-> [-> [-> [Hsat [Hlen Hval]]]]]]].
    exists ((τ, ς) :: Σ').
    repeat split; try done.
    - apply list_subseteq_cons_iff.
      by split; first apply elem_of_flat.
    - solve_length.
    - by apply Forall2_cons_iff.
Qed.

(* Summaries are reachable from some [main] program *)
Definition reachable_from_program 𝕍 xs vs P Λ τ ε Q e := 
  safe_program 𝕍 (types Λ) e = Some τ ∧
  ux_frame_triple (impls Λ) (e⌊vs [//] xs⌋) P Q ε.
Notation reachable_from_main := (reachable_from_program ∅ [] [] EMP).
(* Semantic interpretation of valid summaries *)
Definition valid_summ_ctx Λ (Σ : summ_ctx) :=
  ∀ τ ς, ς ∈ Σ !!! τ → sat_post (post ∘ ς) ∧
  ∀ v, valid_type v τ → reachable_from_main Λ τ (Ok v) (post (ς v)) (src (ς v)).
(* Properties *)
Lemma reachable_bindings Λ Σ Σ1 Σ2 xs1 xs2 vs1 vs2 τ ε Q e :
  valid_summ_ctx Λ Σ → Σ1 ++ Σ2 ⊆ flat_summ_ctx Σ →
  NoDup (xs1 ++ xs2) → valid_types Σ2 vs2 →
  length xs1 = length Σ1 → length xs2 = length Σ2 →
  length vs1 = length Σ1 → length vs2 = length Σ2 →
  reachable_from_program
    (cons_var_ctx (xs1 ++ xs2) (Σ1 ++ Σ2).*1) (xs1 ++ xs2) (vs1 ++ vs2)
    (zip_asrt (Σ1 ++ Σ2) (vs1 ++ vs2)) Λ τ ε Q e →
  reachable_from_program
    (cons_var_ctx xs1 Σ1.*1) xs1 vs1
    (zip_asrt Σ1 vs1) Λ τ ε Q (bindings xs2 (zip_expr Σ2 vs2) e).
Proof.
  intros Hsumm Hsub Hdup Hval Hlenx1 Hlenx2 Hlenv1 Hlenv2 Hreach; subst.
  rewrite reverse_var_ctx; last first.
  { by apply NoDup_app in Hdup as []. }
  { by rewrite length_fmap. }
  rewrite reverse_var_ctx in Hreach; last first.
  { done. }
  { rewrite length_fmap, 2 length_app; lia. }
  generalize dependent e; generalize dependent Σ1;
    generalize dependent xs2; generalize dependent xs1;
    generalize dependent vs2; generalize dependent vs1.
  induction Σ2 as [|ς Σ2]; simpl in *;
    intros vs1 vs2 Hval Hlenv2 xs1 xs2 Hdup Hlenx2 Σ1 Hsub Hlenx1 Hlenv1 e Hreach.
  + apply nil_length_inv in Hlenx2, Hlenv2; subst.
    rewrite 3 (right_id_L _ (++)) in *.
    by unfold bindings.
  + destruct xs2 as [|x xs2]; first done. inversion Hlenx2 as [Hlenx2'].
    destruct vs2 as [|v vs2]; first done. inversion Hlenv2 as [Hlenv2'].
    assert (x ∉ xs1 ∧ x ∉ xs2) as [Hnin1 Hnin2].
    {
      subst; apply NoDup_app in Hdup as [_ [Hnin []%NoDup_cons]].
      by split; first (intros Hin%Hnin; apply Hin; left).
    }
    apply Forall2_cons_iff in Hval as [Hval Hval'].
    rewrite cons_middle, app_assoc in Hdup.
    rewrite cons_middle, app_assoc in Hsub.
    rewrite 2 cons_middle, 2 app_assoc in Hreach.
    rewrite (cons_middle v), app_assoc in Hreach.
    assert (length (xs1 ++ [x]) = length (Σ1 ++ [ς]))
      as Hlenx1' by by rewrite 2 length_app; simpl; lia.
    assert (length (vs1 ++ [v]) = length (Σ1 ++ [ς]))
      as Hlenv1' by by rewrite 2 length_app; simpl; lia.
    assert (ς.2 ∈ Σ !!! ς.1) as [_ Hreach']%Hsumm.
    {
      eapply elem_of_flat, elem_of_subseteq; last done.
      apply elem_of_app; left. apply elem_of_app; right.
      by destruct ς; left.
    }
    specialize (Hreach' v) as [Hsafe' Hux']; first done.
    specialize (IHΣ2
      _ _ Hval' Hlenv2'
      _ _ Hdup Hlenx2'
      _ Hsub Hlenx1' Hlenv1'
      _ Hreach) as [Hsafe Hux].
    split; simpl.
    - eapply safe_main_Some in Hsafe' as ->.
      rewrite insert_var_ctx; last by rewrite 2 length_reverse; solve_length.
      by rewrite <- 2 reverse_snoc, <- list_fmap_singleton, <- fmap_app.
    - unfold bindings; simpl.
      apply safe_main_closed in Hsafe'.
      rewrite let_subst; try done; last solve_length.
      eapply (let_spec _ _ _ _ _ _ (zip_asrt (Σ1 ++ [ς]) (vs1 ++ [v]))).
      * rewrite fmap_app, zip_with_app, fmap_app; last solve_length.
        by eapply frame_app_spec.
      * by rewrite subst_vals_subst; last solve_length.
Qed.
Lemma derivable_for_main Λ Σ e τ Q ε :
  valid_summ_ctx Λ Σ → derivable_post (safe_context Σ) Λ τ ε Q e →
  reachable_from_main Λ τ ε Q e.
Proof.
  intros Hsumm [f [τs [Htype [vs [P [es [Hctx [L [Hspec [xs [-> [Hlenx Hdup]]]]]]]]]]]].
  apply context_soundness in Hctx as [Σ' [Hsub [-> [-> [-> [_ [Hlenv Hval]]]]]]].
  apply ux_frame_soundness in Hspec.
  assert (length xs = length Σ') as Hlenx'.
  { rewrite Hlenx, length_fmap, length_zip_with, length_fmap. lia. }
  apply (reachable_bindings _ _ [] _ [] _ [] _ _ _ _ _
    Hsumm Hsub Hdup Hval eq_refl Hlenx' eq_refl Hlenv
  ); split.
  + by apply safe_call; first solve_length.
  + rewrite subst_call_args; try done; solve_length.
Qed.
(* Soundness *)
Theorem summ_ctx_soundness Λ Σ :
  wf_summ_ctx Λ Σ → valid_summ_ctx Λ Σ.
Proof.
  intros Hsumm. induction Hsumm as [|? ? ? ? ? Hrefute].
  + intros τ ς Hin. destruct τ.
    - rewrite lookup_total_base, elem_of_list_singleton in Hin; subst.
      simpl. split; first apply val_post_sat.
      intros v <-. unfold reachable_from_main, subst_terms; simpl.
      by split; last apply pure_val_spec.
    - rewrite lookup_total_custom in Hin. inversion Hin.
  + intros τ' ς' Hin.
    destruct Hrefute as [τ [λQ [λe [-> [[v Hsat] Hpost]]]]].
    destruct (decide (τ = τ')) as [<-|].
    - rewrite lookup_total_update in Hin.
      apply elem_of_cons in Hin as [->|]; last by eapply IHHsumm.
      split; first by eexists. by intros; eapply derivable_for_main.
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
  intros [Σ [Hctx%summ_ctx_soundness [τ [ε [Q [Hpost [Hsat Hε]]]]]]].
  eapply derivable_for_main in Hpost as [? Hux%ux_triple_preservation]; last done.
  destruct Hsat as [?[?[->]]%Hux].
  destruct ε; first by exfalso; apply Hε; eexists.
  all: by eexists; split; last eexists.
Qed.
