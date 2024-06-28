From RUXt.lang Require Export lang.
From RUXt.lib Require Import gmap.


(*** Termination ***)

(* Error values *)
Inductive error := BotE.
(* Miss values *)
Inductive miss := MLoc (l : loc) | MFun (f : string).
(* Termination tags *)
Inductive exit := Ok (v : value) | Err (ξ : error) | Miss (m : miss).
(* Evalutation errors *)
Definition pure_to_exit (p : pure) : exit :=
  match eval_pure p with
  | Some v => Ok v
  | None => Err BotE
  end.


(* Function implementations *)
Record fun_impl := { params : list string; body : expr }.
Notation "{ ( xs ) e }" := {| params := xs; body := e |}.
Definition impl_ctx : Set := gmap string fun_impl.
(* Heaps *)
Inductive heap_val := LangVal (v : value) | Poison | Freed.
Definition heap : Set := gmap loc heap_val.

(*** Operational semantics ***)

(* Inference rules *)
Reserved Notation "γ ⊢ ⟨ h1 | e ⟩ ⇓ ⟨ h2 | ε ⟩"
  (at level 100, no associativity).
Inductive eval_expr : impl_ctx → heap → expr → heap → exit → Prop :=
| O_Pure : forall γ p h, 
  γ ⊢ ⟨ h | Pure p ⟩ ⇓ ⟨ h | pure_to_exit p ⟩
| O_Error : ∀ γ h, 
  γ ⊢ ⟨ h | Error ⟩ ⇓ ⟨ h | Err BotE ⟩
| O_Assume : ∀ γ p h,
  pure_to_exit p = Ok (VBool true) →
  γ ⊢ ⟨ h | Assume p ⟩ ⇓ ⟨ h | Ok VUnit ⟩
| O_Let : ∀ γ x e1 e2 h h' h'' v ε,
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h'' | Ok v ⟩ → γ ⊢ ⟨ h'' | subst x v e2 ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_LetCut : ∀ γ x e1 e2 h h' ε,
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | ε ⟩ → ((∃ ξ, ε = Err ξ) ∨ (∃ m, ε = Miss m)) →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
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
| O_AllocFreed : ∀ γ h l,
  h !! l = Some Freed →
  γ ⊢ ⟨ h | Alloc ⟩ ⇓ ⟨ <[l:=Poison]>h | Ok (VLoc l) ⟩
| O_AlMLociss : ∀ γ h l, 
  l ∉ dom h →
  γ ⊢ ⟨ h | Alloc ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Free : ∀ γ p h l v,
  pure_to_exit p = Ok (VLoc l) → h !! l = Some v → v ≠ Freed →
  γ ⊢ ⟨ h | Free p ⟩ ⇓ ⟨ <[l:=Freed]>h | Ok VUnit ⟩
| O_FreeFreed : ∀ γ p h l,
  pure_to_exit p = Ok (VLoc l) → h !! l = Some Freed →
  γ ⊢ ⟨ h | Free p ⟩ ⇓ ⟨ h | Err BotE ⟩
| O_FreeMiss : ∀ γ p h l,
  pure_to_exit p = Ok (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Free p ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Store : ∀ γ p1 p2 h l v1 v2,
  pure_to_exit p1 = Ok (VLoc l) → h !! l = Some v1 → v1 ≠ Freed → pure_to_exit p2 = Ok v2 →
  γ ⊢ ⟨ h | Store p1 p2 ⟩ ⇓ ⟨ <[l:=LangVal v2]>h | Ok VUnit⟩
| O_StoreFreed : ∀ γ p1 p2 h l,
  pure_to_exit p1 = Ok (VLoc l) → h !! l = Some Freed →
  γ ⊢ ⟨ h | Store p1 p2 ⟩ ⇓ ⟨ h | Err BotE ⟩
| O_StoreMiss : ∀ γ p1 p2 h l,
  pure_to_exit p1 = Ok (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Store p1 p2 ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Load : ∀ γ p h l v,
  pure_to_exit p = Ok (VLoc l) → h !! l = Some (LangVal v) →
  γ ⊢ ⟨ h | Load p ⟩ ⇓ ⟨ h | Ok v ⟩
| O_LoadFreed : ∀ γ p h l v,
  pure_to_exit p = Ok (VLoc l) → h !! l = Some v → v = Freed ∨ v = Poison →
  γ ⊢ ⟨ h | Load p ⟩ ⇓ ⟨ h | Err BotE ⟩
| O_LoadMiss : ∀ γ p h l,
  pure_to_exit p = Ok (VLoc l) → l ∉ dom h →
  γ ⊢ ⟨ h | Load p ⟩ ⇓ ⟨ h | Miss (MLoc l) ⟩
| O_Call : ∀ γ f i e ps h h' ε,
  γ !! f = Some i → subst_l_pure (params i) ps (body i) = Some e → γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Call f ps ⟩ ⇓ ⟨ h' | ε ⟩
| O_CallMiss : ∀ γ f ps h,
  γ !! f = None →
  γ ⊢ ⟨ h | Call f ps ⟩ ⇓ ⟨ h | Miss (MFun f) ⟩
where "γ ⊢ ⟨ h1 | e ⟩ ⇓ ⟨ h2 | ε ⟩" := (eval_expr γ h1 e h2 ε).

(* Under-approximate frame validity - frame addition *)
Theorem ux_frame γ h e h' ε :
  γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩ →
  ((∃ v, ε = Ok v) ∨ (∃ ξ, ε = Err ξ)) →
  ∀ hF γF, h' ##ₘ hF → γ ##ₘ γF → γ ∪ γF ⊢ ⟨ h ∪ hF | e ⟩ ⇓ ⟨ h' ∪ hF | ε ⟩ ∧ h ##ₘ hF.
Proof.
  intros Hstep Hexit.
  induction Hstep; intros hF γF Hframe' Hγ.
  + split; last done. apply O_Pure.
  + split; last done. apply O_Error.
  + split; last done. by apply O_Assume.
  + assert ((∃ v0 : value, Ok v = Ok v0) ∨ (∃ ξ : error, Ok v = Err ξ))
      as Hexists by (by left; exists v).
    specialize (IHHstep2 Hexit hF γF Hframe' Hγ) as [Hstep2F Hframe''].
    specialize (IHHstep1 Hexists hF γF Hframe'' Hγ) as [Hstep1F Hframe].
    split; last done. by eapply O_Let.
  + specialize (IHHstep Hexit hF γF Hframe' Hγ) as [HstepF Hframe].
    split; last done. by apply O_LetCut.
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
    rewrite <- (insert_union_l h hF l Poison).
    split; last done. apply O_AllocFreed.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. apply O_AlMLociss.
    destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
  + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
    rewrite <- (insert_union_l h hF l Freed).
    split; last done. eapply O_Free; try done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. eapply O_FreeFreed; first done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. apply O_FreeMiss; first done.
    destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
  + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
    rewrite <- (insert_union_l h hF l (LangVal v2)).
    split; last done. eapply O_Store; try done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. eapply O_StoreFreed; first done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. apply O_StoreMiss; first done.
    destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
  + split; last done. eapply O_Load; first done.
    rewrite (lookup_union_Some_raw h hF); by left.
  + split; last done. eapply O_LoadFreed; try done.
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
    left. split; last done. apply O_Pure.
  + exists hs. split; first done.
    left. split; last done. apply O_Error.
  + exists hs. split; first done.
    left. split; last done. by apply O_Assume.
  + specialize (IHHstep1 hs hF γs γF Hheap Hframe Hfun Hγ) as [hs'' [Hframe'' Hstep1F]].
    destruct Hstep1F as [[Hstep1F Hheap'']|[m [Hmiss Hdom]]].
    - specialize (IHHstep2 hs'' hF γs γF Hheap'' Hframe'' Hfun Hγ) as [hs' [Hframe' Hstep2F]].
      exists hs'. split; first done.
      destruct Hstep2F as [[Hstep2F Hheap']|[m [Hmiss Hdom]]].
      * left. split; last done. by eapply O_Let.
      * right. exists m. split; last done. by eapply O_Let.
    - exists hs''. split; first done.
      right. exists m. split; last done. apply O_LetCut; first done. right. by exists m.
  + specialize (IHHstep hs hF γs γF Hheap Hframe Hfun Hγ) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. split; last done. by eapply O_LetCut.
    - right. exists m. split; last done. apply O_LetCut; first done. right. by exists m.
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
  + subst; assert ((hs ∪ hF) !! l = Some Freed) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - exists (<[l:=Poison]>hs). split; first by (apply map_disjoint_insert; first exists Freed).
      left. split; last by rewrite <- (insert_union_l hs hF). by apply O_AllocFreed.
    - exists hs. split; first done.
      right. exists (MLoc l). split; first by apply O_AlMLociss, not_elem_of_dom.
      left. exists l. split; first done. by apply (map_union_dom hs); first exists Freed.
  + exists hs. split; first done.
    left. split; last done. apply O_AlMLociss. set_solver.
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
    - left. split; last done. by eapply O_FreeFreed.
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
    - left. split; last done. by eapply O_StoreFreed.
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
    subst; assert ((hs ∪ hF) !! l = Some v) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_LoadFreed.
    - right. exists (MLoc l). split; first by apply O_LoadMiss, not_elem_of_dom.
      left. exists l. split; first done. by apply (map_union_dom hs); first exists v.
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
