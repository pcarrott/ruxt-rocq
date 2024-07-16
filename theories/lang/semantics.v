From RUXt.lang Require Import lang.
From RUXt.lib Require Import gmap.


(* Program context *)

(* Function implementations *)
Record fun_impl := { params : list string; body : expr }.
Notation "{ ( xs ) e }" := {| params := xs; body := e |}.
Definition impl_ctx : Set := gmap string fun_impl.
(* Heaps *)
Inductive heap_value := LangVal (v : val) | Poison | Freed.
Definition heap : Set := gmap loc heap_value.


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
Definition var_to_exit (t : term) : exit := option_to_exit (eval_var t).
Definition pure_to_exit (p : pure) : exit := option_to_exit (eval_pure p).

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
Reserved Notation "γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩"
  (at level 100, no associativity).
Inductive eval_expr : impl_ctx → heap → expr → heap → exit → Prop :=
| O_Pure : ∀ γ p h v, 
  pure_to_exit p = Ok v →
  γ ⊢ ⟨ h | Pure p ⟩ ⇓ ⟨ h | Ok v ⟩
| O_Error : ∀ γ h, 
  γ ⊢ ⟨ h | Error ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_Assume : ∀ γ t h,
  var_to_exit t = Ok (VBool true) →
  γ ⊢ ⟨ h | Assume t ⟩ ⇓ ⟨ h | Ok VUnit ⟩
| O_Let : ∀ γ x e1 e2 h h' h'' v ε,
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h'' | Ok v ⟩ → γ ⊢ ⟨ h'' | subst x v e2 ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_LetErr : ∀ γ x e1 e2 h h' ξ,
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | Err ξ ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | Err ξ ⟩
| O_LetMiss : ∀ γ x e1 e2 h h' m,
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | Miss m ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | Miss m ⟩
| O_Choice1 : ∀ γ e1 e2 h h' ε,
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Choice e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_Choice2 : ∀ γ e1 e2 h h' ε,
  γ ⊢ ⟨ h | e2 ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Choice e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_Loop : ∀ γ e h h' ε,
  γ ⊢ ⟨ h | Let BAnon e (Loop e) ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Loop e ⟩ ⇓ ⟨ h' | ε ⟩
| O_LoopCut : ∀ γ e h,
  γ ⊢ ⟨ h | Loop e ⟩ ⇓ ⟨ h | Ok VUnit ⟩
| O_Alloc : ∀ γ h l,
  l ∉ dom h →
  γ ⊢ ⟨ h | Alloc ⟩ ⇓ ⟨ <[l:=Poison]>h | Ok (VLoc l) ⟩
| O_Free : ∀ γ t h l v,
  var_to_exit t = Ok (VLoc l) → h !! l = Some v → v ≠ Freed →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ <[l:=Freed]>h | Ok VUnit ⟩
| O_FreeErr : ∀ γ t h l,
  var_to_exit t = Ok (VLoc l) → h !! l = Some Freed →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_FreeMiss : ∀ γ t h l,
  var_to_exit t = Ok (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Store : ∀ γ t1 t2 h l v1 v2,
  var_to_exit t1 = Ok (VLoc l) → h !! l = Some v1 → v1 ≠ Freed → var_to_exit t2 = Ok v2 →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ <[l:=LangVal v2]>h | Ok VUnit⟩
| O_StoreErr : ∀ γ t1 t2 h l,
  var_to_exit t1 = Ok (VLoc l) → h !! l = Some Freed →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_StoreMiss : ∀ γ t1 t2 h l,
  var_to_exit t1 = Ok (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Load : ∀ γ t h l v,
  var_to_exit t = Ok (VLoc l) → h !! l = Some (LangVal v) →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Ok v ⟩
| O_LoadErr : ∀ γ t h l hv,
  var_to_exit t = Ok (VLoc l) → h !! l = Some hv → hv = Freed ∨ hv = Poison →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Err ECrash ⟩
| O_LoadMiss : ∀ γ t h l,
  var_to_exit t = Ok (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Call : ∀ γ f i e ts h h' ε,
  γ !! f = Some i → subst_l_var (params i) ts (body i) = Some e → γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Call f ts ⟩ ⇓ ⟨ h' | ε ⟩
| O_CallMiss : ∀ γ f ts h,
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
  + split; last done. apply O_Error.
  + split; last done. by apply O_Assume.
  + assert ((∃ v0 : val, Ok v = Ok v0) ∨ (∃ ξ : error, Ok v = Err ξ))
      as Hexists by (by left; exists v).
    specialize (IHHstep2 Hexit hF γF Hframe' Hγ) as [Hstep2F Hframe''].
    specialize (IHHstep1 Hexists hF γF Hframe'' Hγ) as [Hstep1F Hframe].
    split; last done. by eapply O_Let.
  + specialize (IHHstep Hexit hF γF Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_LetErr.
  + specialize (IHHstep Hexit hF γF Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_LetMiss.
  + specialize (IHHstep Hexit hF γF Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_Choice1.
  + specialize (IHHstep Hexit hF γF Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_Choice2.
  + specialize (IHHstep Hexit hF γF Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_Loop.
  + split; last done. apply O_LoopCut.
  + apply map_disjoint_insert_l in Hframe' as [HNone Hframe].
    rewrite <- (insert_union_l h hF l Poison).
    split; last done. apply O_Alloc.
    rewrite <- not_elem_of_dom in HNone; set_solver.
  + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
    rewrite <- (insert_union_l h hF l Freed).
    split; last done. eapply O_Free; try done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. eapply O_FreeErr; first done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. apply O_FreeMiss; first done.
    destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
  + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
    rewrite <- (insert_union_l h hF l (LangVal v2)).
    split; last done. eapply O_Store; try done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. eapply O_StoreErr; first done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. apply O_StoreMiss; first done.
    destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
  + split; last done. eapply O_Load; first done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. eapply O_LoadErr; try done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. apply O_LoadMiss; first done.
    destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
  + specialize (IHHstep Hexit hF γF Hframe' Hγ) as [HstepF Hframe].
    split; last done. eapply O_Call; try done.
    rewrite (lookup_union_Some_raw γ γF); by left.
  + split; last done. apply O_CallMiss; try done.
    destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
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
  + exists hs. split; first done.
    left. split; last done. by apply O_Pure.
  + exists hs. split; first done.
    left. split; last done. apply O_Error.
  + exists hs. split; first done.
    left. split; last done. by apply O_Assume.
  + specialize (IHHstep1 hs hF γs γF Hheap Hframe Hfun Hγ) as [hs'' [Hframe'' Hstep1F]].
    destruct Hstep1F as [[Hstep1F Hheap'']|[ms [Hmiss Hdom]]].
    - specialize (IHHstep2 hs'' hF γs γF Hheap'' Hframe'' Hfun Hγ) as [hs' [Hframe' Hstep2F]].
      exists hs'. split; first done.
      destruct Hstep2F as [[Hstep2F Hheap']|[ms [Hmiss Hdom]]].
      * left. split; last done. by eapply O_Let.
      * right. exists ms. split; last done. by eapply O_Let.
    - exists hs''. split; first done.
      right. exists ms. split; last done. by apply O_LetMiss.
  + specialize (IHHstep hs hF γs γF Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[ms [Hmiss Hdom]]].
    - left. split; last done. by apply O_LetErr.
    - right. exists ms. split; last done. by apply O_LetMiss.
  + specialize (IHHstep hs hF γs γF Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[ms [Hmiss Hdom]]].
    - left. split; last done. by apply O_LetMiss.
    - right. exists ms. split; last done. by apply O_LetMiss.
  + specialize (IHHstep hs hF γs γF Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. split; last done. by apply O_Choice1.
    - right. exists m. split; last done. by apply O_Choice1.
  + specialize (IHHstep hs hF γs γF Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. split; last done. by apply O_Choice2.
    - right. exists m. split; last done. by apply O_Choice2.
  + specialize (IHHstep hs hF γs γF Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. split; last done. by apply O_Loop.
    - right. exists m. split; last done. by apply O_Loop.
  + exists hs. split; first done. left.
    split; last done. apply O_LoopCut.
  + exists (<[l:=Poison]>hs). split.
    { apply map_disjoint_insert_l_2; last done. apply not_elem_of_dom. set_solver. }
    left. split; last by rewrite <- (insert_union_l hs hF), Hheap. apply O_Alloc. set_solver.
  + subst; assert ((hs ∪ hF) !! l = Some v) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - exists (<[l:=Freed]>hs). split; first by (apply map_disjoint_insert; first exists v).
      left. split; last by rewrite <- (insert_union_l hs hF). by eapply O_Free.
    - exists hs. split; first done.
      right. exists (MLoc l). split; first by apply O_FreeMiss, not_elem_of_dom.
      left. exists l. split; first done. by apply (map_union_dom hs); first exists v.
  + exists hs. split; first done.
    subst; assert ((hs ∪ hF) !! l = Some Freed) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_FreeErr.
    - right. exists (MLoc l). split; first by apply O_FreeMiss, not_elem_of_dom.
      left. exists l. split; first done. by apply (map_union_dom hs); first exists Freed.
  + exists hs. split; first done.
    left. split; last done. apply O_FreeMiss; first done. set_solver.
  + subst; assert ((hs ∪ hF) !! l = Some v1) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - exists (<[l:=LangVal v2]>hs). split; first by (apply map_disjoint_insert; first exists v1).
      left. split; last by rewrite <- (insert_union_l hs hF). by eapply O_Store.
    - exists hs. split; first done.
      right. exists (MLoc l). split; first by apply O_StoreMiss, not_elem_of_dom.
      left. exists l. split; first done. by apply (map_union_dom hs); first exists v1.
  + exists hs. split; first done.
    subst; assert ((hs ∪ hF) !! l = Some Freed) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_StoreErr.
    - right. exists (MLoc l). split; first by apply O_StoreMiss, not_elem_of_dom.
      left. exists l. split; first done. by apply (map_union_dom hs); first exists Freed.
  + exists hs. split; first done.
    left. split; last done. apply O_StoreMiss; first done. set_solver.
  + exists hs. split; first done.
    subst; assert ((hs ∪ hF) !! l = Some (LangVal v)) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_Load.
    - right. exists (MLoc l). split; first by apply O_LoadMiss, not_elem_of_dom.
      left. exists l. split; first done. by apply (map_union_dom hs); first exists (LangVal v).
  + exists hs. split; first done.
    subst; assert ((hs ∪ hF) !! l = Some hv) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_LoadErr.
    - right. exists (MLoc l). split; first by apply O_LoadMiss, not_elem_of_dom.
      left. exists l. split; first done. by apply (map_union_dom hs); first exists hv.
  + exists hs. split; first done.
    left. split; last done. apply O_LoadMiss; first done. set_solver.
  + specialize (IHHstep hs hF γs γF Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    subst; assert ((γs ∪ γF) !! f = Some i) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - exists hs'. split; first done.
      destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
      * left. split; last done. eapply O_Call; try done.
      * right. exists m. split; last done. eapply O_Call; try done.
    - exists hs. split; first done.
      right. exists (MFun f). split; first by eapply O_CallMiss.
      right. exists f. split; first done. by apply (map_union_dom γs); first exists i.
  + exists hs. split; first done.
    left. split; last done. apply O_CallMiss.
    subst; assert ((γs ∪ γF) !! f = None) as Hlookup by done.
    by apply lookup_union_None in Hlookup as [].
Qed.
