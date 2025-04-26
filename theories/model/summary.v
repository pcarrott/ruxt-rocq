From RUXt.lib Require Export gmap.
From RUXt.lang Require Export assertion.
From RUXt.model Require Export typechecker logic.


(* Summaries for type spaces *)
Record concrete_summary := mk_summary { post : asrt; src : expr }.
Definition summary := val → concrete_summary.
Definition base_summary (kind : base_type) : summary :=
  λ v, mk_summary (val_post kind v) (Pure (PVal v)).
(* Summary contexts *)
Definition summ_ctx := gmap tid (list summary).
Definition insert_base_summary kind Σ : summ_ctx :=
  <[TyBase kind := [base_summary kind]]>Σ.
Definition base_summ_ctx : summ_ctx :=
  foldr insert_base_summary ∅ [TyInt; TyBool; TyLoc; TyUnit].
Lemma lookup_total_base kind :
  base_summ_ctx !!! (TyBase kind) = [base_summary kind].
Proof.
  unfold base_summ_ctx.
  Notation lookup_base l kind := (foldr insert_base_summary ∅ l !!! TyBase kind).
  destruct (decide (kind = TyInt)) as [->|]; first apply lookup_total_insert.
  replace (_ _ _ _ !!! _) with (lookup_base [TyBool; TyLoc; TyUnit] kind) by 
    by symmetry; eapply lookup_total_insert_ne; congruence.
  destruct (decide (kind = TyBool)) as [->|]; first apply lookup_total_insert.
  replace (_ _ _ _ !!! _) with (lookup_base [TyLoc; TyUnit] kind) by 
    by symmetry; eapply lookup_total_insert_ne; congruence.
  destruct (decide (kind = TyLoc)) as [->|]; first apply lookup_total_insert.
  replace (_ _ _ _ !!! _) with (lookup_base [TyUnit] kind) by 
    by symmetry; eapply lookup_total_insert_ne; congruence.
  destruct (decide (kind = TyUnit)) as [->|]; first apply lookup_total_insert.
  replace (_ _ _ _ !!! _) with (lookup_base [] kind) by 
    by symmetry; eapply lookup_total_insert_ne; congruence.
  by destruct kind.
Qed.
Lemma lookup_total_custom n :
  base_summ_ctx !!! (TyCustom n) = [].
Proof.
  unfold base_summ_ctx.
  Notation lookup_custom l n := (foldr insert_base_summary ∅ l !!! TyCustom n).
  replace (_ _ _ _ !!! _) with (lookup_custom [TyBool; TyLoc; TyUnit] n) by
    by symmetry; eapply lookup_total_insert_ne.
  replace (_ _ _ _ !!! _) with (lookup_custom [TyLoc; TyUnit] n) by
    by symmetry; eapply lookup_total_insert_ne.
  replace (_ _ _ _ !!! _) with (lookup_custom [TyUnit] n) by
    by symmetry; eapply lookup_total_insert_ne.
  replace (_ _ _ _ !!! _) with (lookup_custom [] n) by
    by symmetry; eapply lookup_total_insert_ne.
  done.
Qed.

(* Overloading definitions *)
Definition summ_cons (ς : summary) o :=
  match o with None => Some [ς] | Some l => Some (ς :: l) end.
Definition update ς τ (Σ : summ_ctx) := partial_alter (summ_cons ς) τ Σ.
Definition subseteq (Σ Σ' : summ_ctx) : Prop := ∀ τ, Σ !!! τ ⊆ Σ' !!! τ.
Notation "Σ [⊆] Σ'" := (subseteq Σ Σ') (at level 50).
(* Properties *)
Lemma lookup_total_update m i x :
  update x i m !!! i = x :: m !!! i.
Proof.
  rewrite (lookup_total_alt (update _ _ m)).
  unfold update, default. rewrite (lookup_partial_alter _ m).
  destruct (m !! i) as [l|] eqn:Heq.
  + replace (m !! i) with (Some l).
    by rewrite (lookup_total_correct m i l).
  + rewrite (lookup_total_alt m i).
    by replace (m !! i) with (None : option (list summary)).
Qed.
Lemma lookup_total_update_ne m i j x :
  i ≠ j → update x i m !!! j = m !!! j.
Proof.
  intros Hneq. rewrite (lookup_total_alt m).
  unfold update, default. case_match.
  + eapply lookup_total_correct.
    by rewrite (lookup_partial_alter_ne _ m).
  + rewrite (lookup_total_alt (partial_alter _ _ m)).
    by replace (partial_alter (summ_cons x) i m !! j)
      with (None : option (list summary));
      last rewrite (lookup_partial_alter_ne _ m).
Qed.

(* Flatten a summary context into a list of pairs (type, summary) *)
Definition flatten (τ : tid) (ςs : list summary) := map (λ ς, (τ, ς)) ςs.
Definition flat_summ_ctx (Σ : summ_ctx) : list (tid * summary) :=
  map_fold (λ τ ςs a, a ++ flatten τ ςs) [] Σ.
(* Properties *)
Lemma elem_of_flatten τς τ ςs :
  τς ∈ flatten τ ςs ↔ τ = τς.1 ∧ τς.2 ∈ ςs.
Proof.
  split.
  + intros Hin. induction ςs as [|ς' ςs]; first inversion Hin.
    apply elem_of_cons in Hin as [Heq|Hin].
    - inversion Heq; subst.
      by split; last left.
    - apply IHςs in Hin as [-> Hin].
      by split; last right.
  + intros [-> Hin]. induction ςs as [|ς' ςs]; first inversion Hin.
    apply elem_of_cons in Hin as [<-|Hin].
    - by destruct τς; left.
    - by right; apply IHςs.
Qed.
Lemma flat_insert Σ τ ςs τς :
  Σ !! τ = None →
  τς ∈ flat_summ_ctx (<[τ := ςs]>Σ) ↔ τς ∈ (flat_summ_ctx Σ ++ flatten τ ςs).
Proof.
  intros HNone. apply Permutation_spec. unfold flat_summ_ctx.
  rewrite (map_fold_insert (≡ₚ) _ _ _ _ Σ); try done.
  + solve_proper.
  + intros. rewrite <- 2 app_assoc.
    apply Permutation_app_head, Permutation_app_comm.
Qed.
Lemma elem_of_flat Σ τ ς :
  (τ, ς) ∈ flat_summ_ctx Σ ↔ ς ∈ Σ !!! τ.
Proof.
  generalize Σ. eapply map_ind.
  + split; inversion 1.
  + intros τ' ςs Σ' HNone IH.
    split; intros Hin.
    - apply flat_insert in Hin; last done.
      apply elem_of_app in Hin as [Hin|Hin].
      * apply IH in Hin.
        rewrite (lookup_total_insert_ne Σ'); first done.
        rewrite (lookup_total_alt Σ') in Hin.
        destruct (decide (τ' = τ)) as [->|]; last done.
        rewrite HNone in Hin. inversion Hin.
      * apply elem_of_flatten in Hin as [-> Hin].
        by rewrite (lookup_total_insert Σ').
    - apply flat_insert; first done.
      apply elem_of_app. destruct (decide (τ' = τ)) as [->|].
      * rewrite (lookup_total_insert Σ') in Hin.
        right. by apply elem_of_flatten.
      * rewrite (lookup_total_insert_ne Σ') in Hin; last done.
        left. by apply IH.
Qed.
