From stdpp Require Export binders.
From RUXt Require Import gmap.



(* Heap locations *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

(* Language values *)
Inductive val := ValInt (n : Z) | ValLoc (l : loc) | ValBool (b : bool) | ValUnit.
(* Binary operations *)
Inductive bin_op := PlusOp | EqOp.

(* Pure expressions *)
Inductive pure :=
| Val (v : val)
| Var (x : string)
| BinOp (op : bin_op) (p1 p2 : pure).
(* Variable substitution in pure expressions *)
Fixpoint subst_pure (p : pure) (x : string) (v : val) : pure :=
  match p with
  | Val v => Val v
  | Var y => if decide (x = y) then Val v else p
  | BinOp op p1 p2 => BinOp op (subst_pure p1 x v) (subst_pure p2 x v)
  end.

(* Language expressions *)
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
(* Variable substitution in language expressions *)
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
(* Variable substitution with anonymous binders *)
Definition subst (e : expr) (x : binder) (v : val) : expr :=
  match x with BAnon => e | BNamed n => subst_expr e n v end.

(* Heaps *)
Inductive heap_val := LangVal (v : val) | Poison | Freed.
Definition heap := gmap loc heap_val.
(* Error values *)
Inductive error := Crash.
(* Termination tags *)
Inductive exit := Ok (v : val) | Err (ξ : error) | Miss (l : loc).

(* Pure expression evaluation *)
Fixpoint eval_pure (p : pure) : exit :=
  match p with
  | Val v => Ok v
  | Var x => Err Crash
  | BinOp op p1 p2 => 
    match eval_pure p1, eval_pure p2 with
    | Ok v1, Ok v2 =>
      match op, v1, v2 with
      | PlusOp, ValInt z1, ValInt z2 => Ok (ValInt (z1 + z2))
      | EqOp, ValInt z1, ValInt z2 => Ok (ValBool (Z.eqb z1 z2))
      | _, _, _ => Err Crash
      end
    | _, _ => Err Crash
    end
  end.
(* Operational semantics *)
Reserved Notation "<< h1 | e >> ⇓ << h2 | ε >>".
Inductive eval_expr : heap → expr → heap → exit → Prop :=
| O_Pure : forall p h, 
  << h | Pure p >> ⇓ << h | eval_pure p >>
| O_Error : ∀ h, 
  << h | Error >> ⇓ << h | Err Crash >>
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
  << h | Free p >> ⇓ << h | Err Crash >>
| O_FreeMiss : ∀ p h l, eval_pure p = Ok (ValLoc l) → l ∉ dom h →
  << h | Free p >> ⇓ << h | Miss l >>
| O_Store : ∀ p1 p2 h l v1 v2, eval_pure p1 = Ok (ValLoc l) → h !! l = Some v1 → v1 ≠ Freed → eval_pure p2 = Ok v2 →
  << h | Store p1 p2 >> ⇓ << <[l:=LangVal v2]>h | Ok ValUnit>>
| O_StoreFreed : ∀ p1 p2 h l, eval_pure p1 = Ok (ValLoc l) → h !! l = Some Freed →
  << h | Store p1 p2 >> ⇓ << h | Err Crash >>
| O_StoreMiss : ∀ p1 p2 h l, eval_pure p1 = Ok (ValLoc l) → l ∉ dom h →
  << h | Store p1 p2 >> ⇓ << h | Miss l >>
| O_Load : ∀ p h l v, eval_pure p = Ok (ValLoc l) → h !! l = Some (LangVal v) →
  << h | Load p >> ⇓ << h | Ok v >>
| O_LoadFreed : ∀ p h l v, eval_pure p = Ok (ValLoc l) → h !! l = Some v → v = Freed ∨ v = Poison →
  << h | Load p >> ⇓ << h | Err Crash >>
| O_LoadMiss : ∀ p h l, eval_pure p = Ok (ValLoc l) → l ∉ dom h →
  << h | Load p >> ⇓ << h | Miss l >>
where "<< h1 | e >> ⇓ << h2 | ε >>" := (eval_expr h1 e h2 ε).



(* Under-approximate frame validity - frame addition *)
Theorem ux_frame_preserve e h h' ε :
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
    split; last done. by apply O_LetCut.
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
  + split; last done. apply O_AllocMiss.
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
Qed.

(* Over-approximate frame validity - frame subtraction *)
Theorem ox_frame_preserve e h h' ε :
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
      exists hs'. split; first done.
      destruct Hstep2F as [[Hstep2F Hheap']|[l [Hmiss Hdom]]].
      * left. split; last done. by eapply O_Let.
      * right. exists l. split; last done. by eapply O_Let.
    - exists hs''. split; first done.
      right. exists l. split; last done. apply O_LetCut; first done. right. by exists l.
  + specialize (IHHstep hs hF Hheap Hframe) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[l [Hmiss Hdom]]].
    - left. split; last done. by eapply O_LetCut.
    - right. exists l. split; last done. apply O_LetCut; first done. right. by exists l.
  + specialize (IHHstep hs hF Hheap Hframe) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[l [Hmiss Hdom]]].
    - left. split; last done. by apply O_Choice1.
    - right. exists l. split; last done. by apply O_Choice1.
  + specialize (IHHstep hs hF Hheap Hframe) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[l [Hmiss Hdom]]].
    - left. split; last done. by apply O_Choice2.
    - right. exists l. split; last done. by apply O_Choice2.
  + specialize (IHHstep hs hF Hheap Hframe) as [hs' [Hframe' HstepF]].
    exists hs'. split; first done.
    destruct HstepF as [[HstepF Hheap']|[l [Hmiss Hdom]]].
    - left. split; last done. by apply O_Loop.
    - right. exists l. split; last done. by apply O_Loop.
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
      right. exists l. split; last by apply (map_union_dom hs); first exists Freed.
      by apply O_AllocMiss, not_elem_of_dom.
  + exists hs. split; first done.
    left. split; last done. apply O_AllocMiss. set_solver.
  + subst; assert ((hs ∪ hF) !! l = Some v) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - exists (<[l:=Freed]>hs). split; first by (apply map_disjoint_insert; first exists v).
      left. split; last by rewrite <- (insert_union_l hs hF). by eapply O_Free.
    - exists hs. split; first done.
      right. exists l. split; last by apply (map_union_dom hs); first exists v.
      by apply O_FreeMiss, not_elem_of_dom.
  + exists hs. split; first done.
    subst; assert ((hs ∪ hF) !! l = Some Freed) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_FreeFreed.
    - right. exists l. split; last by apply (map_union_dom hs); first exists Freed.
      by apply O_FreeMiss, not_elem_of_dom.
  + exists hs. split; first done.
    left. split; last done. apply O_FreeMiss; first done. set_solver.
  + subst; assert ((hs ∪ hF) !! l = Some v1) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - exists (<[l:=LangVal v2]>hs). split; first by (apply map_disjoint_insert; first exists v1).
      left. split; last by rewrite <- (insert_union_l hs hF). by eapply O_Store.
    - exists hs. split; first done.
      right. exists l. split; last by apply (map_union_dom hs); first exists v1.
      by apply O_StoreMiss, not_elem_of_dom.
  + exists hs. split; first done.
    subst; assert ((hs ∪ hF) !! l = Some Freed) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_StoreFreed.
    - right. exists l. split; last by apply (map_union_dom hs); first exists Freed.
      by apply O_StoreMiss, not_elem_of_dom.
  + exists hs. split; first done.
    left. split; last done. apply O_StoreMiss; first done. set_solver.
  + exists hs. split; first done.
    subst; assert ((hs ∪ hF) !! l = Some (LangVal v)) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. split; last done. by eapply O_Load.
    - right. exists l. split; last by apply (map_union_dom hs); first exists (LangVal v).
      by apply O_LoadMiss, not_elem_of_dom.
  + exists hs. split; first done.
    assert (v = Freed ∨ v = Poison) as [|] by done.
    - subst; assert ((hs ∪ hF) !! l = Some Freed) as Hlookup by done.
      apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
      * left. split; last done. by eapply O_LoadFreed; last left.
      * right. exists l. split; last by apply (map_union_dom hs); first exists Freed.
        by apply O_LoadMiss, not_elem_of_dom.
    - subst; assert ((hs ∪ hF) !! l = Some Poison) as Hlookup by done.
      apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
      * left. split; last done. by eapply O_LoadFreed; last right.
      * right. exists l. split; last by apply (map_union_dom hs); first exists Poison.
        by apply O_LoadMiss, not_elem_of_dom.
  + exists hs. split; first done.
    left. split; last done. apply O_LoadMiss; first done. set_solver.
Qed.
