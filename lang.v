From stdpp Require Export strings.
From stdpp Require Export binders.
From stdpp Require Import gmap.

Definition block : Set := positive.
Definition loc : Set := block * Z.

Inductive val := ValInt (n : Z) | ValLoc (l : loc) | ValBool (b : bool) | ValUnit.

Inductive bin_op := PlusOp | EqOp.

Inductive pure :=
| Val (v : val)
| Var (x : string)
| BinOp (op : bin_op) (p1 p2 : pure).

Inductive expr :=
| Pure (p : pure)
| Error
| Assume (p : pure)
| Let (x : binder) (e1 e2 : expr)
| Choice (e1 e2 : expr)
| Loop (e : expr)
| Alloc
| Free (p : pure)
| Store (p1 p2 : pure)
| Load (p : pure).

Fixpoint subst_pure (p : pure) (x : string) (v : val) : pure :=
    match p with
    | Val v => Val v
    | Var y => if decide (x = y) then Val v else p
    | BinOp op p1 p2 => BinOp op (subst_pure p1 x v) (subst_pure p2 x v)
    end.

Fixpoint subst_expr (e : expr) (x : string) (v : val) : expr :=
    match e with
    | Pure p => Pure (subst_pure p x v)
    | Error => Error
    | Assume p => Assume (subst_pure p x v)
    | Let y e1 e2 => if decide (y = BNamed x) then Let y (subst_expr e1 x v) e2
                     else Let y (subst_expr e1 x v) (subst_expr e2 x v)
    | Choice e1 e2 => Choice (subst_expr e1 x v) (subst_expr e2 x v)
    | Loop e => Loop (subst_expr e x v)
    | Alloc => Alloc
    | Free p => Free (subst_pure p x v)
    | Store p1 p2 => Store (subst_pure p1 x v) (subst_pure p2 x v)
    | Load p => Load (subst_pure p x v)
    end.

Definition subst (e : expr) (x : binder) (v : val) : expr :=
    match x with BAnon => e | BNamed n => subst_expr e n v end.

Inductive error := ErrBot.

Inductive exit := Ok (v : val) | Err (ξ : error) | Miss (l : loc).

Definition eval_binop (op : bin_op) (v1 v2 : val) : exit :=
    match op, v1, v2 with
    | PlusOp, ValInt z1, ValInt z2 => Ok (ValInt (z1 + z2))
    | EqOp, ValInt z1, ValInt z2 => Ok (ValBool (Z.eqb z1 z2))
    | _, _, _ => Err ErrBot
    end.

Fixpoint eval_pure (p : pure) : exit :=
    match p with
    | Val v => Ok v
    | Var x => Err ErrBot
    | BinOp op p1 p2 => 
        match eval_pure p1, eval_pure p2 with
        | Ok v1, Ok v2 => eval_binop op v1 v2
        | _, _ => Err ErrBot
        end
    end.

Inductive heap_val := LangVal (v : val) | Poison | Freed.
Definition heap := gmap loc heap_val.

Reserved Notation "<< h1 | e >> ⇓ << h2 | ε >>".
Inductive eval_expr : expr → heap → exit → heap → Prop :=
| O_Pure : forall p h, 
    << h | Pure p >> ⇓ << h | eval_pure p >>
| O_Error : ∀ h, 
    << h | Error >> ⇓ << h | Err ErrBot >>
| O_Assume : ∀ p h, eval_pure p = Ok (ValBool true) →
    << h | Assume p >> ⇓ << h | Ok ValUnit >>
| O_Let : ∀ x e1 e2 h h' h'' v ε, << h | e1 >> ⇓ << h'' | Ok v >> → << h'' | subst e2 x v >> ⇓ << h' | ε >> →
    << h | Let x e1 e2 >> ⇓ << h' | ε >>
| O_LetCut : ∀ x e1 e2 h h' ε, << h | e1 >> ⇓ << h' | ε >> → ((∃ ξ, ε = Err ξ) ∨ (∃ l, ε = Miss l)) →
    << h | Let x e1 e2 >> ⇓ << h' | ε >>
| O_Choice1 : ∀ e1 e2 h h' ε, << h | e1 >> ⇓ << h' | ε >> →
    << h | Choice e1 e2 >> ⇓ << h' | ε >>
| O_Choice2 : ∀ e1 e2 h h' ε, << h | e2 >> ⇓ << h' | ε >> →
    << h | Choice e1 e2 >> ⇓ << h' | ε >>
| O_Loop : ∀ e h h' ε, << h | Let BAnon e (Loop e) >> ⇓ << h' | ε >> →
    << h | Loop e >> ⇓ << h' | ε >>
| O_LoopCut : ∀ e h,
    << h | Loop e >> ⇓ << h | Ok ValUnit >>
| O_Alloc : ∀ h l, l ∉ dom h →
    << h | Alloc >> ⇓ << <[l:=Poison]>h | Ok (ValLoc l) >>
| O_AllocFreed : ∀ h l, h !! l = Some Freed →
    << h | Alloc >> ⇓ << <[l:=Poison]>h | Ok (ValLoc l) >>
| O_AllocMiss : ∀ h l,  l ∉ dom h →
    << h | Alloc >> ⇓ << h | Miss l >>
| O_Free : ∀ p h l v, eval_pure p = Ok (ValLoc l) → h !! l = Some v → v ≠ Freed →
    << h | Free p >> ⇓ << <[l:=Freed]>h | Ok ValUnit >>
| O_FreeFreed : ∀ p h l, eval_pure p = Ok (ValLoc l) → h !! l = Some Freed →
    << h | Free p >> ⇓ << h | Err ErrBot >>
| O_FreeMiss : ∀ p h l, eval_pure p = Ok (ValLoc l) → l ∉ dom h →
    << h | Free p >> ⇓ << h | Miss l >>
| O_Store : ∀ p1 p2 h l v1 v2, eval_pure p1 = Ok (ValLoc l) → h !! l = Some v1 → v1 ≠ Freed → eval_pure p2 = Ok v2 →
    << h | Store p1 p2 >> ⇓ << <[l:=LangVal v2]>h | Ok ValUnit>>
| O_StoreFreed : ∀ p1 p2 h l, eval_pure p1 = Ok (ValLoc l) → h !! l = Some Freed →
    << h | Store p1 p2 >> ⇓ << h | Err ErrBot >>
| O_StoreMiss : ∀ p1 p2 h l, eval_pure p1 = Ok (ValLoc l) → l ∉ dom h →
    << h | Store p1 p2 >> ⇓ << h | Miss l >>
| O_Load : ∀ p h l v, eval_pure p = Ok (ValLoc l) → h !! l = Some (LangVal v) →
    << h | Load p >> ⇓ << h | Ok v >>
| O_LoadFreed : ∀ p h l v, eval_pure p = Ok (ValLoc l) → h !! l = Some v → v = Freed ∨ v = Poison →
    << h | Load p >> ⇓ << h | Err ErrBot >>
| O_LoadMiss : ∀ p h l, eval_pure p = Ok (ValLoc l) → l ∉ dom h →
    << h | Load p >> ⇓ << h | Miss l >>
where "<< h1 | e >> ⇓ << h2 | ε >>" := (eval_expr e h1 ε h2).



Lemma ux_frame_preserve e h h' ε :
    << h | e >> ⇓ << h' | ε >> →
    ((∃ v, ε = Ok v) ∨ (∃ ξ, ε = Err ξ)) →
    ∀ hF, h' ##ₘ hF → << h ∪ hF | e >> ⇓ << h' ∪ hF | ε >> ∧ h ##ₘ hF.
Proof.
    intros Hstep Hexit.
    induction Hstep; intros hF Hframe'.
    + split; last done. apply O_Pure.
    + split; last done. apply O_Error.
    + split; last done. by apply O_Assume.
    + assert ((∃ v0 : val, Ok v = Ok v0) ∨ (∃ ξ : error, Ok v = Err ξ))
        as Hexists by (by left; exists v).
      specialize (IHHstep2 Hexit hF Hframe') as [Hstep2F Hframe''].
      specialize (IHHstep1 Hexists hF Hframe'') as [Hstep1F Hframe].
      split; last done. by eapply O_Let.
    + specialize (IHHstep Hexit hF Hframe') as [HstepF Hframe].
      split; last done. by eapply O_LetCut.
    + specialize (IHHstep Hexit hF Hframe') as [HstepF Hframe].
      split; last done. by apply O_Choice1.
    + specialize (IHHstep Hexit hF Hframe') as [HstepF Hframe].
      split; last done. by apply O_Choice2.
    + specialize (IHHstep Hexit hF Hframe') as [HstepF Hframe].
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
    + split; last done. eapply O_AllocMiss; try done.
      destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
    + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
      rewrite <- (insert_union_l h hF l Freed).
      split; last done. eapply O_Free; try done.
      rewrite (lookup_union_Some_raw h hF); by left.
    + split; last done. eapply O_FreeFreed; try done.
      rewrite (lookup_union_Some_raw h hF); by left.
    + split; last done. eapply O_FreeMiss; try done.
      destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
    + apply map_disjoint_insert_l in Hframe' as [_ Hframe].
      rewrite <- (insert_union_l h hF l (LangVal v2)).
      split; last done. eapply O_Store; try done.
      rewrite (lookup_union_Some_raw h hF); by left.
    + split; last done. eapply O_StoreFreed; try done.
      rewrite (lookup_union_Some_raw h hF); by left.
    + split; last done. eapply O_StoreMiss; try done.
      destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
    + split; last done. eapply O_Load; try done.
      rewrite (lookup_union_Some_raw h hF); by left.
    + split; last done. eapply O_LoadFreed; try done.
      rewrite (lookup_union_Some_raw h hF); by left.
    + split; last done. eapply O_LoadMiss; try done.
      destruct Hexit as [[? Hmiss]|[? Hmiss]]; inversion Hmiss.
Qed.

Lemma ox_frame_preserve e h h' ε :
    << h | e >> ⇓ << h' | ε >> →
    ∀ hs hF, h = hs ∪ hF → hs ##ₘ hF →
    ∃ hs', hs' ##ₘ hF ∧ (
        (<< hs | e >> ⇓ << hs' | ε >> ∧ h' = hs' ∪ hF) ∨
        (∃ l, << hs | e >> ⇓ << hs' | Miss l >> ∧ l ∈ dom hF)
    ).
Proof.
    intros Hstep.
    induction Hstep; intros hs hF Hheap Hframe.
    + exists hs. split; first done.
      left. split; last done. apply O_Pure.
    + exists hs. split; first done.
      left. split; last done. apply O_Error.
    + exists hs. split; first done.
      left. split; last done. by apply O_Assume.
    + specialize (IHHstep1 hs hF Hheap Hframe) as [hs'' [Hframe'' Hstep1F]].
      destruct Hstep1F as [[Hstep1F Hheap'']|[l [Hmiss Hdom]]].
      - specialize (IHHstep2 hs'' hF Hheap'' Hframe'') as [hs' [Hframe' Hstep2F]].
        destruct Hstep2F as [[Hstep2F Hheap']|[l [Hmiss Hdom]]].
        * exists hs'. split; first done. left.
          split; last done. by eapply O_Let.
        * exists hs'. split; first done. right.
          exists l. split; last done. by eapply O_Let.
      - exists hs''. split; first done. right.
        exists l. split; last done. apply O_LetCut; first done. right. by exists l.
    + specialize (IHHstep hs hF Hheap Hframe) as [hs' [Hframe' HstepF]].
      destruct HstepF as [[HstepF Hheap']|[l [Hmiss Hdom]]].
      - exists hs'. split; first done. left.
        split; last done. by eapply O_LetCut.
      - exists hs'. split; first done. right.
        exists l. split; last done. apply O_LetCut; first done. right. by exists l.
    + specialize (IHHstep hs hF Hheap Hframe) as [hs' [Hframe' HstepF]].
      destruct HstepF as [[HstepF Hheap']|[l [Hmiss Hdom]]].
      - exists hs'. split; first done. left.
        split; last done. by apply O_Choice1.
      - exists hs'. split; first done. right.
        exists l. split; last done. by apply O_Choice1.
    + specialize (IHHstep hs hF Hheap Hframe) as [hs' [Hframe' HstepF]].
      destruct HstepF as [[HstepF Hheap']|[l [Hmiss Hdom]]].
      - exists hs'. split; first done. left.
        split; last done. by apply O_Choice2.
      - exists hs'. split; first done. right.
        exists l. split; last done. by apply O_Choice2.
    + specialize (IHHstep hs hF Hheap Hframe) as [hs' [Hframe' HstepF]].
      destruct HstepF as [[HstepF Hheap']|[l [Hmiss Hdom]]].
      - exists hs'. split; first done. left.
        split; last done. by apply O_Loop.
      - exists hs'. split; first done. right.
        exists l. split; last done. by apply O_Loop.
    + exists hs. split; first done. left.
      split; last done. apply O_LoopCut.
    + exists (<[l:=Poison]>hs). split.
      { apply map_disjoint_insert_l_2; last done.
        rewrite <- not_elem_of_dom. set_solver. }
      left. split; last by rewrite <- (insert_union_l hs hF), Hheap.
      apply O_Alloc. set_solver.
    + assert (hs !! l = Some Freed ∨ hs !! l = None ∧ hF !! l = Some Freed) as Hlookup.
      { by subst; apply lookup_union_Some_raw. }
      destruct Hlookup as [HSome|[HNone _]].
      - exists (<[l:=Poison]>hs). split.
        { apply map_disjoint_insert_l_2; last done.
          by apply (map_disjoint_Some_l hs hF l Freed). }
        left. split; last by rewrite <- (insert_union_l hs hF), Hheap.
        by apply O_AllocFreed.
      - exists hs. split; first done.
        right. exists l. split; last first.
        { subst; assert (is_Some ((hs ∪ hF) !! l)) as HSome by by exists Freed.
          apply lookup_union_is_Some in HSome as [HSome|HSome].
          * apply not_elem_of_dom in HNone. destruct HNone. by apply elem_of_dom.
          * by apply elem_of_dom. }
        by apply O_AllocMiss, not_elem_of_dom.
    + exists hs. split; first done. left.
      split; last done. apply O_AllocMiss. set_solver.
    + assert (hs !! l = Some v ∨ hs !! l = None ∧ hF !! l = Some v) as Hlookup.
      { by subst; apply lookup_union_Some_raw. }
      destruct Hlookup as [HSome|[HNone _]].
      - exists (<[l:=Freed]>hs). split.
        { apply map_disjoint_insert_l_2; last done.
          by apply (map_disjoint_Some_l hs hF l v). }
        left. split; last by rewrite <- (insert_union_l hs hF), Hheap.
        by eapply O_Free.
      - exists hs. split; first done.
        right. exists l. split; last first.
        { subst; assert (is_Some ((hs ∪ hF) !! l)) as HSome by by exists v.
          apply lookup_union_is_Some in HSome as [HSome|HSome].
          * apply not_elem_of_dom in HNone. destruct HNone. by apply elem_of_dom.
          * by apply elem_of_dom. }
        by apply O_FreeMiss, not_elem_of_dom.
    + assert (hs !! l = Some Freed ∨ hs !! l = None ∧ hF !! l = Some Freed) as Hlookup.
      { by subst; apply lookup_union_Some_raw. }
      destruct Hlookup as [HSome|[HNone _]].
      - exists hs. split; first done.
        left. split; last done. by eapply O_FreeFreed.
      - exists hs. split; first done.
        right. exists l. split; last first.
        { subst; assert (is_Some ((hs ∪ hF) !! l)) as HSome by by exists Freed.
          apply lookup_union_is_Some in HSome as [HSome|HSome].
          * apply not_elem_of_dom in HNone. destruct HNone. by apply elem_of_dom.
          * by apply elem_of_dom. }
        by apply O_FreeMiss, not_elem_of_dom.
    + exists hs. split; first done. left.
      split; last done. apply O_FreeMiss; first done. set_solver.
    + assert (hs !! l = Some v1 ∨ hs !! l = None ∧ hF !! l = Some v1) as Hlookup.
      { by subst; apply lookup_union_Some_raw. }
      destruct Hlookup as [HSome|[HNone _]].
      - exists (<[l:=LangVal v2]>hs). split.
        { apply map_disjoint_insert_l_2; last done.
          rewrite map_disjoint_alt in Hframe; specialize (Hframe l).
          destruct Hframe; last done.
          by assert (Some v1 = None) by by rewrite <- HSome. }
        left. split; last by rewrite <- (insert_union_l hs hF), Hheap.
        by eapply O_Store.
      - exists hs. split; first done.
        right. exists l. split; last first.
        { subst; assert (is_Some ((hs ∪ hF) !! l)) as HSome by by exists v1.
          apply lookup_union_is_Some in HSome as [HSome|HSome].
          * apply not_elem_of_dom in HNone. destruct HNone. by apply elem_of_dom.
          * by apply elem_of_dom. }
        by apply O_StoreMiss, not_elem_of_dom.
    + assert (hs !! l = Some Freed ∨ hs !! l = None ∧ hF !! l = Some Freed) as Hlookup.
      { by subst; apply lookup_union_Some_raw. }
      destruct Hlookup as [HSome|[HNone _]].
      - exists hs. split; first done.
        left. split; last done. by eapply O_StoreFreed.
      - exists hs. split; first done.
        right. exists l. split; last first.
        { subst; assert (is_Some ((hs ∪ hF) !! l)) as HSome by by exists Freed.
          apply lookup_union_is_Some in HSome as [HSome|HSome].
          * apply not_elem_of_dom in HNone. destruct HNone. by apply elem_of_dom.
          * by apply elem_of_dom. }
        by apply O_StoreMiss, not_elem_of_dom.
    + exists hs. split; first done. left.
      split; last done. apply O_StoreMiss; first done. set_solver.
    + assert (hs !! l = Some (LangVal v) ∨ hs !! l = None ∧ hF !! l = Some (LangVal v)) as Hlookup.
      { by subst; apply lookup_union_Some_raw. }
      destruct Hlookup as [HSome|[HNone _]].
      - exists hs. split; first done.
        left. split; last done. by eapply O_Load.
      - exists hs. split; first done.
        right. exists l. split; last first.
        { subst; assert (is_Some ((hs ∪ hF) !! l)) as HSome by by exists (LangVal v).
          apply lookup_union_is_Some in HSome as [HSome|HSome].
          * apply not_elem_of_dom in HNone. destruct HNone. by apply elem_of_dom.
          * by apply elem_of_dom. }
        by apply O_LoadMiss, not_elem_of_dom.
    + destruct H1.
      - assert (hs !! l = Some Freed ∨ hs !! l = None ∧ hF !! l = Some Freed) as Hlookup.
        { by subst; apply lookup_union_Some_raw. }
        destruct Hlookup as [HSome|[HNone _]].
        * exists hs. split; first done.
          left. split; last done. by eapply O_LoadFreed; last left.
        * exists hs. split; first done.
          right. exists l. split; last first.
          { subst; assert (is_Some ((hs ∪ hF) !! l)) as HSome by by exists Freed.
          apply lookup_union_is_Some in HSome as [HSome|HSome].
          * apply not_elem_of_dom in HNone. destruct HNone. by apply elem_of_dom.
          * by apply elem_of_dom. }
          by apply O_LoadMiss, not_elem_of_dom.
      - assert (hs !! l = Some Poison ∨ hs !! l = None ∧ hF !! l = Some Poison) as Hlookup.
        { by subst; apply lookup_union_Some_raw. }
        destruct Hlookup as [HSome|[HNone _]].
        * exists hs. split; first done.
          left. split; last done. by eapply O_LoadFreed; last right.
        * exists hs. split; first done.
          right. exists l. split; last first.
          { subst; assert (is_Some ((hs ∪ hF) !! l)) as HSome by by exists Poison.
          apply lookup_union_is_Some in HSome as [HSome|HSome].
          * apply not_elem_of_dom in HNone. destruct HNone. by apply elem_of_dom.
          * by apply elem_of_dom. }
          by apply O_LoadMiss, not_elem_of_dom.
    + exists hs. split; first done. left.
      split; last done. apply O_LoadMiss; first done. set_solver.
Qed.