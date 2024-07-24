From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.


(* Program context *)

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
(* Evalutation errors *)
Definition option_to_exit (o : option val) : exit :=
  match o with Some v => Ok v | None => Err ECrash end.
Notation "⌊ t ⌋ₜ" := (option_to_exit (eval_term t)) (at level 50).
Notation "⌊ p ⌋ₚ" := (option_to_exit (eval_pure p)) (at level 50).

(* Properties *)
Lemma pure_neg_Ok p z :
  ⌊ p ⌋ₚ = Ok (VInt z) → ⌊ PNeg p ⌋ₚ = Ok (VInt (-z)).
Proof.
  intros Hok. simpl.
  destruct (eval_pure p); last by exfalso.
  by inversion Hok; subst; simpl.
Qed.
Lemma pure_not_Ok p b :
  ⌊ p ⌋ₚ = Ok (VBool b) → ⌊ PNot p ⌋ₚ = Ok (VBool (negb b)).
Proof.
  intros Hok. simpl.
  destruct (eval_pure p); last by exfalso.
  by inversion Hok; subst; simpl.
Qed.
Lemma pure_plus_Ok p1 p2 z1 z2 :
  ⌊ p1 ⌋ₚ = Ok (VInt z1) → ⌊ p2 ⌋ₚ = Ok (VInt z2) →
  ⌊ PPlus p1 p2 ⌋ₚ = Ok (VInt (z1 + z2)).
Proof.
  intros Hok1 Hok2. simpl.
  destruct (eval_pure p1); destruct (eval_pure p2); try by exfalso.
  by inversion Hok1; inversion Hok2; subst; simpl.
Qed.
Lemma pure_eq_Ok p1 p2 z1 z2 :
  ⌊ p1 ⌋ₚ = Ok (VInt z1) → ⌊ p2 ⌋ₚ = Ok (VInt z2) →
  ⌊ PEq p1 p2 ⌋ₚ = Ok (VBool (Z.eqb z1 z2)).
Proof.
  intros Hok1 Hok2. simpl.
  destruct (eval_pure p1); destruct (eval_pure p2); try by exfalso.
  by inversion Hok1; inversion Hok2; subst; simpl.
Qed.

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
  ⌊ p ⌋ₚ = Ok v →
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
| O_Choice1 γ e1 e2 h h' ε :
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Choice e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_Choice2 γ e1 e2 h h' ε :
  γ ⊢ ⟨ h | e2 ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Choice e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_Loop γ e h h' ε :
  γ ⊢ ⟨ h | Let BAnon e (Loop e) ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Loop e ⟩ ⇓ ⟨ h' | ε ⟩
| O_LoopCut γ e h :
  γ ⊢ ⟨ h | Loop e ⟩ ⇓ ⟨ h | Ok VUnit ⟩
| O_Alloc γ h l :
  l ∉ dom h →
  γ ⊢ ⟨ h | Alloc ⟩ ⇓ ⟨ <[l:=Poison]>h | Ok (VLoc l) ⟩
| O_Free γ t h l v :
  ⌊ t ⌋ₜ = Ok (VLoc l) → h !! l = Some v → v ≠ Freed →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ <[l:=Freed]>h | Ok VUnit ⟩
| O_FreeErr γ t h l :
  ⌊ t ⌋ₜ = Ok (VLoc l) → h !! l = Some Freed →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_FreeMiss γ t h l :
  ⌊ t ⌋ₜ = Ok (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Store γ t1 t2 h l v1 v2 :
  ⌊ t1 ⌋ₜ = Ok (VLoc l) → h !! l = Some v1 → v1 ≠ Freed → ⌊ t2 ⌋ₜ = Ok v2 →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ <[l:=LangVal v2]>h | Ok VUnit⟩
| O_StoreErr γ t1 t2 h l :
  ⌊ t1 ⌋ₜ = Ok (VLoc l) → h !! l = Some Freed →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_StoreMiss γ t1 t2 h l :
  ⌊ t1 ⌋ₜ = Ok (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Load γ t h l v :
  ⌊ t ⌋ₜ = Ok (VLoc l) → h !! l = Some (LangVal v) →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Ok v ⟩
| O_LoadErr γ t h l hv :
  ⌊ t ⌋ₜ = Ok (VLoc l) → h !! l = Some hv → hv = Freed ∨ hv = Poison →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_LoadMiss γ t h l :
  ⌊ t ⌋ₜ = Ok (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Call γ f xs e ts h h' ε :
  γ !! f = Some {(xs) e} → γ ⊢ ⟨ h | e⌊ts[//]xs⌋ₜ ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Call f ts ⟩ ⇓ ⟨ h' | ε ⟩
| O_CallMiss γ f ts h :
  γ !! f = None →
  γ ⊢ ⟨ h | Call f ts ⟩ ⇓ ⟨ h | Miss (MFun f) ⟩
where "γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩" := (eval_expr γ h e h' ε).

(* Under-approximate frame validity - frame addition *)
Theorem ux_frame γ h e h' ε :
  γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩ →
  ((∃ v, ε = Ok v) ∨ (∃ ξ, ε = Err ξ)) →
  ∀ hF γF, h' ##ₘ hF → γ ##ₘ γF → γ ∪ γF ⊢ ⟨ h ∪ hF | e ⟩ ⇓ ⟨ h' ∪ hF | ε ⟩ ∧ h ##ₘ hF.
Proof.
  intros Hstep Hexit.
  induction Hstep; intros hF γF Hframe' Hγ.
  + split; last done. by apply O_Pure.
  + split; last done. by apply O_Assume.
  + split; last done. by apply O_Error.
  + assert ((∃ v', Ok v = Ok v') ∨ (∃ ξ, Ok v = Err ξ)) as Hexists by (by left; eexists).
    specialize (IHHstep2 Hexit _ _ Hframe' Hγ) as [Hstep2F Hframe''].
    specialize (IHHstep1 Hexists _ _ Hframe'' Hγ) as [Hstep1F Hframe].
    split; last done. by eapply O_Let.
  + specialize (IHHstep Hexit _ _ Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_LetErr.
  + specialize (IHHstep Hexit _ _ Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_LetMiss.
  + specialize (IHHstep Hexit _ _ Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_Choice1.
  + specialize (IHHstep Hexit _ _ Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_Choice2.
  + specialize (IHHstep Hexit _ _ Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_Loop.
  + split; last done. by apply O_LoopCut.
  + apply map_disjoint_insert_l in Hframe' as [HNone Hframe].
    rewrite <- (insert_union_l h).
    split; last done. apply O_Alloc.
    rewrite <- not_elem_of_dom in HNone; set_solver.
  + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
    rewrite <- (insert_union_l h).
    split; last done. eapply O_Free; try done.
    apply lookup_union_Some_raw; by left.
  + split; last done. eapply O_FreeErr; try done.
    apply lookup_union_Some_raw; by left.
  + split; last done. destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
  + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
    rewrite <- (insert_union_l h).
    split; last done. eapply O_Store; try done.
    apply lookup_union_Some_raw; by left.
  + split; last done. eapply O_StoreErr; try done.
    apply lookup_union_Some_raw; by left.
  + split; last done. destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
  + split; last done. eapply O_Load; try done.
    apply lookup_union_Some_raw; by left.
  + split; last done. eapply O_LoadErr; try done.
    apply lookup_union_Some_raw; by left.
  + split; last done. destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
  + specialize (IHHstep Hexit _ _ Hframe' Hγ) as [HstepF Hframe].
    split; last done. eapply O_Call; try done.
    apply lookup_union_Some_raw; by left.
  + split; last done. destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
Qed.

(* Over-approximate frame validity - frame subtraction *)
Theorem ox_frame γ h e h' ε :
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
    left. split; last done. by apply O_Pure.
  + eexists. split; first done.
    left. split; last done. by apply O_Assume.
  + eexists. split; first done.
    left. split; last done. by apply O_Error.
  + specialize (IHHstep1 _ _ _ _ Hheap Hframe Hfun Hγ) as [hs'' [Hframe'' Hstep1F]].
    destruct Hstep1F as [[Hstep1F Hheap'']|[ms [Hmiss Hdom]]].
    - specialize (IHHstep2 _ _ _ _ Hheap'' Hframe'' Hfun Hγ) as [hs' [Hframe' Hstep2F]].
      eexists. split; first done.
      destruct Hstep2F as [[Hstep2F Hheap']|[ms [Hmiss Hdom]]].
      * left. split; last done. by eapply O_Let.
      * right. eexists. split; last done. by eapply O_Let.
    - eexists. split; first done.
      right. eexists. split; last done. by apply O_LetMiss.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[ms [Hmiss Hdom]]].
    - left. split; last done. by apply O_LetErr.
    - right. eexists. split; last done. by apply O_LetMiss.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[ms [Hmiss Hdom]]].
    - left. split; last done. by apply O_LetMiss.
    - right. eexists. split; last done. by apply O_LetMiss.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. split; last done. by apply O_Choice1.
    - right. eexists. split; last done. by apply O_Choice1.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. split; last done. by apply O_Choice2.
    - right. eexists. split; last done. by apply O_Choice2.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. split; last done. by apply O_Loop.
    - right. eexists. split; last done. by apply O_Loop.
  + eexists. split; first done. left.
    split; last done. by apply O_LoopCut.
  + eexists. split; first by subst; apply map_disjoint_union_insert. left.
    split; last by rewrite <- insert_union_l, Hheap. apply O_Alloc. set_solver.
  + subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - eexists. split; first by (apply map_disjoint_insert; first eexists).
      left. split; last by rewrite <- insert_union_l. by eapply O_Free.
    - eexists. split; first done.
      right. eexists. split; first by apply O_FreeMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_FreeErr.
    - right. eexists. split; first by apply O_FreeMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply O_FreeMiss; first done. set_solver.
  + subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - eexists. split; first by (apply map_disjoint_insert; first eexists).
      left. split; last by rewrite <- insert_union_l. by eapply O_Store.
    - eexists. split; first done.
      right. eexists. split; first by apply O_StoreMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_StoreErr.
    - right. eexists. split; first by apply O_StoreMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply O_StoreMiss; first done. set_solver.
  + eexists. split; first done.
    subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_Load.
    - right. eexists. split; first by apply O_LoadMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_LoadErr.
    - right. eexists. split; first by apply O_LoadMiss, not_elem_of_dom.
      left. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply O_LoadMiss; first done. set_solver.
  + specialize (IHHstep _ _ _ _ Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    subst; assert (_ !! f = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - eexists. split; first done.
      destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
      * left. split; last done. by eapply O_Call.
      * right. eexists. split; last done. by eapply O_Call.
    - exists hs. split; first done.
      right. eexists. split; first by eapply O_CallMiss.
      right. eexists. split; first done. by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply O_CallMiss.
    by eapply (lookup_union_None γs γF); subst.
Qed.
