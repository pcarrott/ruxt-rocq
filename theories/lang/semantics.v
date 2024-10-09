From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.


(*** Program context ***)

(* Function implementations *)
Record fun_impl := mk_fun_impl { params : list string; body : expr }.
Notation "{ ( xs ) e }" := (mk_fun_impl xs e).
Definition impl_ctx := gmap string fun_impl.
(* Heaps *)
Inductive heap_value := LangVal (v : val) | Poison | Freed.
Definition heap := gmap loc heap_value.


(*** Termination ***)

(* Error values *)
Inductive error := ECrash.
(* Miss values *)
Inductive miss := MLoc (l : loc) | MFun (f : string).
(* Termination tags *)
Inductive exit := Ok (v : val) | Err (ξ : error) | Miss (m : miss).

(* Equality *)
Global Instance error_eq_dec : EqDecision error.
Proof. solve_decision. Defined.
Global Instance miss_eq_dec : EqDecision miss.
Proof. solve_decision. Defined.
Global Instance exit_eq_dec : EqDecision exit.
Proof. solve_decision. Defined.

(* Countability *)
Global Instance error_countable : Countable error.
Proof.
  refine (inj_countable' (λ ξ, match ξ with ECrash => () end)
  (λ u, match u with () => ECrash end) _); by intros [].
Qed.
Global Instance miss_countable : Countable miss.
Proof.
  refine (inj_countable' (λ m, match m with MLoc l => inl l | MFun f => inr f end)
  (λ s, match s with inl l => MLoc l | inr f => MFun f end) _); by intros [].
Qed.
Global Instance exit_countable : Countable exit.
Proof.
  refine (inj_countable' (λ ε, match ε with
  | Ok v => (inl (inl v)) | Err ξ => (inl (inr ξ)) | Miss m => (inr m)
  end) (λ s, match s with
  | (inl (inl v)) => Ok v | (inl (inr ξ)) => Err ξ | (inr m) => Miss m
  end) _); by intros [].
Qed.


(*** Operational semantics ***)

(* Inference rules *)
Reserved Notation "γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩" (at level 50).
Inductive eval_expr : impl_ctx → heap → expr → heap → exit → Prop :=
| O_Pure γ p h v :
  ⌊ p ⌋ₚ = Some v →
  γ ⊢ ⟨ h | Pure p ⟩ ⇓ ⟨ h | Ok v ⟩
| O_Assume γ h :
  γ ⊢ ⟨ h | Assume TTrue ⟩ ⇓ ⟨ h | Ok VUnit ⟩
| O_Error γ h :
  γ ⊢ ⟨ h | Error ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_Let γ x e1 e2 h h' h'' v ε :
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h'' | Ok v ⟩ → γ ⊢ ⟨ h'' | e2⌊v//x⌋ ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_LetErr γ x e1 e2 h h' ξ :
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | Err ξ ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | Err ξ ⟩
| O_LetMiss γ x e1 e2 h h' m :
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | Miss m ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | Miss m ⟩
| O_Choice γ ei e1 e2 h h' ε :
  γ ⊢ ⟨ h | ei ⟩ ⇓ ⟨ h' | ε ⟩ → (ei = e1 ∨ ei = e2) →
  γ ⊢ ⟨ h | Choice e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_Alloc γ h l :
  l ∉ dom h →
  γ ⊢ ⟨ h | Alloc ⟩ ⇓ ⟨ <[l:=Poison]>h | Ok (VLoc l) ⟩
| O_Free γ t h l v :
  ⌊ t ⌋ₜ = Some (VLoc l) → h !! l = Some v → v ≠ Freed →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ <[l:=Freed]>h | Ok VUnit ⟩
| O_FreeErr γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) → h !! l = Some Freed →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_FreeMiss γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Store γ t1 t2 h l v1 v2 :
  ⌊ t1 ⌋ₜ = Some (VLoc l) → h !! l = Some v1 → v1 ≠ Freed → ⌊ t2 ⌋ₜ = Some v2 →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ <[l:=LangVal v2]>h | Ok VUnit⟩
| O_StoreErr γ t1 t2 h l :
  ⌊ t1 ⌋ₜ = Some (VLoc l) → h !! l = Some Freed →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_StoreMiss γ t1 t2 h l :
  ⌊ t1 ⌋ₜ = Some (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Load γ t h l v :
  ⌊ t ⌋ₜ = Some (VLoc l) → h !! l = Some (LangVal v) →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Ok v ⟩
| O_LoadErr γ t h l hv :
  ⌊ t ⌋ₜ = Some (VLoc l) → h !! l = Some hv → hv = Freed ∨ hv = Poison →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_LoadMiss γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Call γ f xs e ts h h' ε :
  γ !! f = Some {(xs) e} → γ ⊢ ⟨ h | e⌊ts[//]xs⌋ₜ ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Call f ts ⟩ ⇓ ⟨ h' | ε ⟩
| O_CallMiss γ f ts h :
  γ !! f = None →
  γ ⊢ ⟨ h | Call f ts ⟩ ⇓ ⟨ h | Miss (MFun f) ⟩
where "γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩" := (eval_expr γ h e h' ε).

(* Under-approximate frame validity - frame addition *)
Theorem frame_addition γ h e h' ε :
  γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩ →
  ∀ hF γF, h' ##ₘ hF → γ ##ₘ γF →
  (γ ∪ γF ⊢ ⟨ h ∪ hF | e ⟩ ⇓ ⟨ h' ∪ hF | ε ⟩ ∧ h ##ₘ hF) ∨
  (∃ m, ε = Miss m ∧ (
    (∃ l, m = MLoc l ∧ l ∈ dom hF) ∨ (∃ f, m = MFun f ∧ f ∈ dom γF)
  )).
Proof.
  intros Hstep.
  induction Hstep; intros hF γF Hframe' Hγ.
  + left. by split; first apply O_Pure.
  + left. by split; first apply O_Assume.
  + left. by split; first apply O_Error.
  + specialize (IHHstep2 _ _ Hframe' Hγ) as [[Hstep2F Hframe'']|]; last by right.
    specialize (IHHstep1 _ _ Hframe'' Hγ) as [[Hstep1F Hframe]|[?[]]]; last by exfalso.
    left. by split; first eapply O_Let.
  + specialize (IHHstep _ _ Hframe' Hγ) as [[HstepF Hframe]|]; last by right.
    left. by split; first apply O_LetErr.
  + specialize (IHHstep _ _ Hframe' Hγ) as [[HstepF Hframe]|]; last by right.
    left. by split; first apply O_LetMiss.
  + specialize (IHHstep _ _ Hframe' Hγ) as [[HstepF Hframe]|]; last by right.
    left. by split; first eapply O_Choice.
  + apply map_disjoint_insert_l in Hframe' as [HNone Hframe].
    rewrite <- (insert_union_l h).
    left. split; last done. apply O_Alloc.
    rewrite <- not_elem_of_dom in HNone; set_solver.
  + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
    rewrite <- (insert_union_l h).
    left. split; last done. eapply O_Free; try done.
    apply lookup_union_Some_raw; by left.
  + left. split; last done. eapply O_FreeErr; try done.
    apply lookup_union_Some_raw; by left.
  + destruct (hF !! l) as [hv|] eqn:Hlookup.
    - right. eexists. split; first done. left. eexists. split; first done.
      apply elem_of_dom. by eexists.
    - left. split; last done. eapply O_FreeMiss; try done.
      assert (l ∉ dom h) as Hnin by assumption.
      intros Hin%dom_union. apply Hnin.
      apply elem_of_union in Hin as []; first done.
      rewrite <- not_elem_of_dom in Hlookup. by exfalso.
  + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
    rewrite <- (insert_union_l h).
    left. split; last done. eapply O_Store; try done.
    apply lookup_union_Some_raw; by left.
  + left. split; last done. eapply O_StoreErr; try done.
    apply lookup_union_Some_raw; by left.
  + destruct (hF !! l) as [hv|] eqn:Hlookup.
    - right. eexists. split; first done. left. eexists. split; first done.
      apply elem_of_dom. by eexists.
    - left. split; last done. eapply O_StoreMiss; try done.
      assert (l ∉ dom h) as Hnin by assumption.
      intros Hin%dom_union. apply Hnin.
      apply elem_of_union in Hin as []; first done.
      rewrite <- not_elem_of_dom in Hlookup. by exfalso.
  + left. split; last done. eapply O_Load; try done.
    apply lookup_union_Some_raw; by left.
  + left. split; last done. eapply O_LoadErr; try done.
    apply lookup_union_Some_raw; by left.
  + destruct (hF !! l) as [hv|] eqn:Hlookup.
    - right. eexists. split; first done. left. eexists. split; first done.
      apply elem_of_dom. by eexists.
    - left. split; last done. eapply O_LoadMiss; try done.
      assert (l ∉ dom h) as Hnin by assumption.
      intros Hin%dom_union. apply Hnin.
      apply elem_of_union in Hin as []; first done.
      rewrite <- not_elem_of_dom in Hlookup. by exfalso.
  + specialize (IHHstep _ _ Hframe' Hγ) as [[HstepF Hframe]|]; last by right.
    left. split; last done. eapply O_Call; try done.
    apply lookup_union_Some_raw; by left.
  + destruct (γF !! f) as [hv|] eqn:Hlookup.
    - right. eexists. split; first done. right. eexists. split; first done.
      apply elem_of_dom. by eexists.
    - left. split; last done. eapply O_CallMiss; try done.
      by apply lookup_union_None.
Qed.

(* Over-approximate frame validity - frame subtraction *)
Theorem frame_subtraction γ h e h' ε :
  γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩ →
  ∀ hs hF γs γF, h = hs ∪ hF → hs ##ₘ hF → γ = γs ∪ γF → γs ##ₘ γF →
  ∃ hs', hs' ##ₘ hF ∧ (
    (γs ⊢ ⟨ hs | e ⟩ ⇓ ⟨ hs' | ε ⟩ ∧ h' = hs' ∪ hF) ∨
    (∃ m, γs ⊢ ⟨ hs | e ⟩ ⇓ ⟨ hs' | Miss m ⟩ ∧ (
      (∃ l, m = MLoc l ∧ l ∈ dom hF) ∨ (∃ f, m = MFun f ∧ f ∈ dom γF)
    ))
  ).
Proof.
  intros Hstep.
  induction Hstep; intros hs hF γs γF Hheap Hframe Hfun Hγ.
  + eexists. split; first done.
    left. by split; first apply O_Pure.
  + eexists. split; first done.
    left. by split; first apply O_Assume.
  + eexists. split; first done.
    left. by split; first apply O_Error.
  + specialize (IHHstep1 _ _ _ _ Hheap Hframe Hfun Hγ) as [hs'' [Hframe'' Hstep1F]].
    destruct Hstep1F as [[Hstep1F Hheap'']|[ms [Hmiss Hdom]]].
    - specialize (IHHstep2 _ _ _ _ Hheap'' Hframe'' Hfun Hγ) as [hs' [Hframe' Hstep2F]].
      eexists. split; first done.
      destruct Hstep2F as [[Hstep2F Hheap']|[ms [Hmiss Hdom]]].
      * left. by split; first eapply O_Let.
      * right. eexists. by split; first eapply O_Let.
    - eexists. split; first done.
      right. eexists. by split; first apply O_LetMiss.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[ms [Hmiss Hdom]]].
    - left. by split; first apply O_LetErr.
    - right. eexists. by split; first apply O_LetMiss.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[ms [Hmiss Hdom]]].
    - left. by split; first apply O_LetMiss.
    - right. eexists. by split; first apply O_LetMiss.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. by split; first eapply O_Choice.
    - right. eexists. by split; first eapply O_Choice.
  + eexists. split; first by subst; apply map_disjoint_union_insert. left.
    split; last by rewrite <- insert_union_l, Hheap. apply O_Alloc. set_solver.
  + subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - eexists. split; first by eapply map_disjoint_Some_insert.
      left. split; last by rewrite <- insert_union_l. by eapply O_Free.
    - eexists. split; first done.
      right. eexists. split; first by apply O_FreeMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply O_FreeErr.
    - right. eexists. split; first by apply O_FreeMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply O_FreeMiss; first done. set_solver.
  + subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - eexists. split; first by eapply map_disjoint_Some_insert.
      left. split; last by rewrite <- insert_union_l. by eapply O_Store.
    - eexists. split; first done.
      right. eexists. split; first by apply O_StoreMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply O_StoreErr.
    - right. eexists. split; first by apply O_StoreMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply O_StoreMiss; first done. set_solver.
  + eexists. split; first done.
    subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply O_Load.
    - right. eexists. split; first by apply O_LoadMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply O_LoadErr.
    - right. eexists. split; first by apply O_LoadMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply O_LoadMiss; first done. set_solver.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    subst; assert (_ !! f = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - eexists. split; first done.
      destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
      * left. by split; first eapply O_Call.
      * right. eexists. by split; first eapply O_Call.
    - exists hs. split; first done.
      right. eexists. split; first by eapply O_CallMiss.
      right. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply O_CallMiss.
    by eapply (lookup_union_None γs γF); subst.
Qed.
