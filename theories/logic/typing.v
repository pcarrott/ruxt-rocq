From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.
From RUXt.lang Require Import semantics.
From RUXt.assertion Require Export hprop.
From RUXt.assertion.types Require Export int bool unit own.


(*** Over-approximate specifications ***)

(* Function types *)
Record fun_type := mk_fun_type { ty_in : list type; ty_out : type }.
Notation "{ τs ↣ τ }" := (mk_fun_type τs τ).
Definition type_ctx := gmap string fun_type.

(* Typing rules *)
Reserved Notation "Δ ∣ 𝕋 ⊢ e ⊣ λ𝕌" (at level 50).
Inductive ty_rule : type_ctx → (list typing) → expr → (val → list typing) → Prop :=
| T_Int Δ z :
  Δ ∣ [] ⊢ Pure (PInt z) ⊣ λ v, [v ⊲ int]
| T_Bool Δ b :
  Δ ∣ [] ⊢ Pure (PBool b) ⊣ λ v, [v ⊲ bool]
| T_Unit Δ :
  Δ ∣ [] ⊢ Pure PUnit ⊣ λ v, [v ⊲ unit]
| T_Minus Δ p :
  Δ ∣ [] ⊢ Pure p ⊣ (λ v, [v ⊲ int]) →
  Δ ∣ [] ⊢ Pure (PMinus p) ⊣ λ v, [v ⊲ int]
| T_Not Δ p :
  Δ ∣ [] ⊢ Pure p ⊣ (λ v, [v ⊲ bool]) →
  Δ ∣ [] ⊢ Pure (PNot p) ⊣ λ v, [v ⊲ bool]
| T_Add Δ p1 p2 :
  Δ ∣ [] ⊢ Pure p1 ⊣ (λ v, [v ⊲ int]) → Δ ∣ [] ⊢ Pure p2 ⊣ (λ v, [v ⊲ int]) →
  Δ ∣ [] ⊢ Pure (PAdd p1 p2) ⊣ λ v, [v ⊲ int]
| T_Le Δ p1 p2 :
  Δ ∣ [] ⊢ Pure p1 ⊣ (λ v, [v ⊲ int]) → Δ ∣ [] ⊢ Pure p2 ⊣ (λ v, [v ⊲ int]) →
  Δ ∣ [] ⊢ Pure (PLe p1 p2) ⊣ λ v, [v ⊲ bool]
| T_Assume Δ b :
  Δ ∣ [] ⊢ Assume (TBool b) ⊣ λ _, []
| T_Let Δ x e1 e2 𝕋 λ𝕌 λ𝕍 :
  Δ ∣ 𝕋 ⊢ e1 ⊣ λ𝕍 → (∀ v', Δ ∣ λ𝕍 v' ⊢ e2⌊v'//x⌋ ⊣ λ𝕌) →
  Δ ∣ 𝕋 ⊢ Let x e1 e2 ⊣ λ𝕌
| T_Choice Δ e1 e2 𝕋 𝕌 :
  Δ ∣ 𝕋 ⊢ e1 ⊣ (λ v, 𝕌) → Δ ∣ 𝕋 ⊢ e2 ⊣ (λ v, 𝕌) →
  Δ ∣ 𝕋 ⊢ Choice e1 e2 ⊣ λ v, 𝕌
| T_Val Δ v' τ :
  Δ ∣ [v' ⊲ τ] ⊢ Pure (PVal v') ⊣ λ v, [v ⊲ τ]
| T_Alloc Δ :
  Δ ∣ [] ⊢ Alloc (TInt 1) ⊣ λ vl, [vl ⊲ empty]
| T_Free Δ vl τ :
  Δ ∣ [vl ⊲ own τ] ⊢ Free (TVal vl) ⊣ λ _, []
| T_Store Δ v vl τ1 τ2 :
  Δ ∣ [vl ⊲ own τ1; v ⊲ τ2] ⊢ Store (TVal vl) (TVal v) ⊣ λ _, [vl ⊲ box τ2]
| T_Load Δ vl τ :
  Δ ∣ [vl ⊲ box τ] ⊢ Load (TVal vl) ⊣ λ v, [v ⊲ τ; vl ⊲ empty]
| T_Frame Δ e 𝕋 𝕌 𝕍 :
  Δ ∣ 𝕋 ⊢ e ⊣ (λ v, 𝕌) →
  Δ ∣ 𝕋 ++ 𝕍 ⊢ e ⊣ λ v, 𝕌 ++ 𝕍
| T_Cons Δ e 𝕋 λ𝕌 𝕋' λ𝕌' :
  𝕋' ⊆+ 𝕋 → (∀ v, λ𝕌 v ⊆+ λ𝕌' v) → Δ ∣ 𝕋' ⊢ e ⊣ λ𝕌' →
  Δ ∣ 𝕋 ⊢ e ⊣ λ𝕌
| T_Call Δ f ts τs τ vs :
  Δ !! f = Some {τs ↣ τ} → ts = TVals vs →
  Δ ∣ vs [⊲] boxes τs ⊢ Call f ts ⊣ λ v, [v ⊲ box τ]
where "Δ ∣ 𝕋 ⊢ e ⊣ λ𝕌" := (ty_rule Δ 𝕋 e λ𝕌).


(*** Soundness ***)

(* Typing rule definition *)
Definition ox_triple (γ : impl_ctx) (e : expr) (P : asrt) (λQ : val → asrt) : Prop :=
  ∀ h, hprop h P → ∀ h' ε, γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩ →
  ∃ v, ε = Ok v ∧ hprop h' (λQ v).
Definition valid_fun_type (γ : impl_ctx) f vs τs τ :=
  ∃ xs e, γ !! f = Some {(xs) e} ∧ ox_triple γ (e⌊vs[//]xs⌋) ([∗ₜ vs [⊲] boxes τs]) (λ v, [∗ₜ [v ⊲ box τ]]).
Definition valid_type_ctx (γ : impl_ctx) (Δ : type_ctx) : Prop :=
  ∀ f τs τ, Δ !! f = Some {τs ↣ τ} →
  ∀ vs, valid_fun_type γ f vs τs τ.
Definition ty_spec (Δ : type_ctx) (e : expr) (𝕋 : list typing) (λ𝕌 : val → list typing) : Prop :=
  ∀ γ, valid_type_ctx γ Δ → ox_triple γ e ([∗ₜ 𝕋]) (λ v, [∗ₜ λ𝕌 v]).

(* Soundness of typing rules *)
Theorem ty_soundness Δ 𝕋 e λ𝕌 :
  Δ ∣ 𝕋 ⊢ e ⊣ λ𝕌 → ty_spec Δ e 𝕋 λ𝕌.
Proof.
  intros rule; induction rule; intros γ Hval h H𝕋 h' ε Hstep.
  + inversion Hstep; subst. eexists. split; first done.
    do 2 eexists. repeat split; first apply map_union_id_l;
      first apply map_disjoint_empty_l. rewrite hiter_singleton.
    by replace v with (VInt z) by (simpl in *; congruence).
  + inversion Hstep; subst. eexists. split; first done.
    do 2 eexists. repeat split; first apply map_union_id_l;
      first apply map_disjoint_empty_l. rewrite hiter_singleton.
    by replace v with (VBool b) by (simpl in *; congruence).
  + inversion Hstep; subst. eexists. split; first done.
    do 2 eexists. repeat split; first apply map_union_id_l;
      first apply map_disjoint_empty_l. rewrite hiter_singleton.
    by replace v with VUnit by (simpl in *; congruence).
  + inversion Hstep; subst. eexists. split; first done.
    do 2 eexists. repeat split; first apply map_union_id_l;
      first apply map_disjoint_empty_l. rewrite hiter_singleton.
    assert (⌊PMinus p⌋ₚ = Some v) as Hpure by assumption. inversion Hpure.
    destruct v; by destruct (eval_pure p) as [v|];
      first destruct v.
  + inversion Hstep; subst. eexists. split; first done.
    do 2 eexists. repeat split; first apply map_union_id_l;
      first apply map_disjoint_empty_l. rewrite hiter_singleton.
    assert (⌊PNot p⌋ₚ = Some v) as Hpure by assumption. inversion Hpure.
    destruct v; by destruct (eval_pure p) as [v|];
      first destruct v.
  + inversion Hstep; subst. eexists. split; first done.
    do 2 eexists. repeat split; first apply map_union_id_l;
      first apply map_disjoint_empty_l. rewrite hiter_singleton.
    assert (⌊PAdd p1 p2⌋ₚ = Some v) as Hpure by assumption. inversion Hpure.
    destruct v; by destruct (eval_pure p1) as [v1|]; destruct (eval_pure p2) as [v2|];
      first (destruct v1; destruct v2).
  + inversion Hstep; subst. eexists. split; first done.
    do 2 eexists. repeat split; first apply map_union_id_l;
      first apply map_disjoint_empty_l. rewrite hiter_singleton.
    assert (⌊PLe p1 p2⌋ₚ = Some v) as Hpure by assumption. inversion Hpure.
    destruct v; by destruct (eval_pure p1) as [v1|]; destruct (eval_pure p2) as [v2|];
      first (destruct v1; destruct v2).
  + inversion Hstep; subst. eexists. split; first done.
    do 2 eexists. repeat split;
      first apply map_union_id_l; first apply map_disjoint_empty_l.
  + inversion Hstep; subst.
    - assert (γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h'' | Ok v ⟩) as Hstep1 by assumption.
      assert (γ ⊢ ⟨ h'' | e2 ⌊ v // x ⌋ ⟩ ⇓ ⟨ h' | ε ⟩) as Hstep2 by assumption.
      assert (∀ v', ty_spec Δ (e2⌊v'//x⌋) (λ𝕍 v') λ𝕌) as IHrule' by assumption.
      specialize (IHrule _ Hval _ H𝕋 _ _ Hstep1) as
        [? [Hok [h𝕍 [htrue [-> [Hdisj𝕍 [H𝕍%own_typings Htrue]]]]]]].
      symmetry in Hok; inversion Hok; subst.
      eapply frame_subtraction in Hstep2 as [h𝕌' [Hdisj𝕌' Hstep2]]; try done;
        last apply map_disjoint_empty_r; last apply map_union_id_r.
      destruct Hstep2 as [[Hstep2 ->]|[m [Hstep2 Hmiss]]].
      * specialize (IHrule' _ _ Hval _ H𝕍 _ _ Hstep2) as
          [? [-> [h𝕌 [htrue' [-> [Hdisj𝕌 [H𝕌 Htrue']]]]]]].
        apply map_disjoint_union_l in Hdisj𝕌' as [? Hdisj𝕌'].
        rewrite <- (assoc_L (∪)). eexists. split; first done.
        do 2 eexists. by repeat split; first apply map_disjoint_union_r.
      * by specialize (IHrule' _ _ Hval _ H𝕍 _ _ Hstep2) as
          [? [Hfalse [h𝕌 [htrue' [-> [Hdisj𝕌 [H𝕌 Htrue']]]]]]].
    - assert (γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | Err ξ ⟩) as Hstep1 by assumption.
      by specialize (IHrule _ Hval _ H𝕋 _ _ Hstep1) as
          [? [Hfalse [h𝕌 [htrue' [-> [Hdisj𝕌 [H𝕌 Htrue']]]]]]].
    - assert (γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | Miss m ⟩) as Hstep1 by assumption.
      by specialize (IHrule _ Hval _ H𝕋 _ _ Hstep1) as
          [? [Hfalse [h𝕌 [htrue' [-> [Hdisj𝕌 [H𝕌 Htrue']]]]]]].
  + inversion Hstep; subst.
    assert (ei = e1 ∨ ei = e2) as [|] by assumption; subst.
    - assert (γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | ε ⟩) as Hstep1 by assumption.
      specialize (IHrule1 _ Hval _ H𝕋 _ _ Hstep1) as
        [? [-> [h𝕌 [htrue [-> [Hdisj𝕌 [H𝕌 Htrue]]]]]]].
      eexists. split; first done. by do 2 eexists.
    - assert (γ ⊢ ⟨ h | e2 ⟩ ⇓ ⟨ h' | ε ⟩) as Hstep2 by assumption.
      specialize (IHrule2 _ Hval _ H𝕋 _ _ Hstep2) as
        [? [-> [h𝕌 [htrue [-> [Hdisj𝕌 [H𝕌 Htrue]]]]]]].
      eexists. split; first done. by do 2 eexists.
  + inversion Hstep; subst. eexists. split; first done.
    replace v with v' in * by (simpl in *; congruence).
    destruct H𝕋 as [hv [htrue [-> [Hdisj [Hv Htrue]]]]].
    by do 2 eexists.
  + inversion Hstep; subst. eexists. split; first done.
    replace n with 1 by (inversion H0; lia).
    do 2 eexists. repeat split; first apply insert_union_singleton_l;
      first by apply map_disjoint_singleton_l, not_elem_of_dom.
    rewrite hiter_singleton. simpl; replace l.2 with 0 by done. by left.
  + destruct H𝕋 as [hl [htrue [-> [Hdisj [Hl Htrue]]]]].
    inversion Hstep; subst.
    - eexists. split; first done. do 2 eexists. repeat split;
        first apply map_union_id_l; first apply map_disjoint_empty_l.
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_singleton in Hl. by apply own_loc in Hl as [? []].
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_singleton in Hl. apply own_loc in Hl as [? [hv]].
      assert ((hl ∪ htrue) !! l.1 = Some Freed)
        as Hfalse%lookup_union_Some_inv_l by assumption;
        last by eapply map_disjoint_Some_l.
      replace (hl !! l.1) with (Some (BVal 1 {[l.2 := hv]})) in Hfalse. congruence.
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_singleton in Hl. apply own_loc in Hl as [? []].
      assert (l.1 ∉ dom (hl ∪ htrue)) as Hfalse by assumption.
      exfalso. apply Hfalse, elem_of_dom. eexists.
      by apply lookup_union_Some_l.
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_singleton in Hl. apply own_loc in Hl as [? [hv]].
      assert ((hl ∪ htrue) !! l.1 = Some (BVal sz bh))
        as HSome%lookup_union_Some_inv_l by assumption;
        last by eapply map_disjoint_Some_l.
      replace (hl !! l.1) with (Some (BVal 1 {[l.2 := hv]})) in HSome.
      inversion HSome; subst. assert (i = 0) as -> by lia.
      replace l.2 with 0 in * by done.
      assert (0 ∉ dom ({[0 := hv]} : block_heap)) as Hfalse by done.
      exfalso. apply Hfalse, elem_of_dom. eexists.
      by apply lookup_singleton.
  + destruct H𝕋 as [h𝕋 [htrue [-> [Hdisj [H𝕋 Htrue]]]]].
    inversion Hstep; subst.
    - eexists. split; first done.
      replace v0 with v in * by (simpl in *; congruence).
      replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_cons in H𝕋. destruct H𝕋 as [hl [hτ2 [-> [Hdisj2 [Hl Hτ2]]]]].
      rewrite hiter_singleton in Hτ2.
      destruct τ1 as [τ1|].
      * destruct Hl as [prev [hl' [hτ1 [-> [Hdisj1 [[->] Hτ1]]]]]].

        apply map_disjoint_union_l in Hdisj2 as []. unfold hstore.
        rewrite (insert_union_l _ htrue), (insert_union_l _ hτ2), (insert_union_l _ hτ1).
        replace (<[l.1 := BVal sz (bupdate bh l.2 v)]> ({[l.1 := BVal 1 {[l.2 := HVal prev]}]}))
          with ({[l.1 := BVal sz (bupdate bh l.2 v)]} : heap) by (symmetry; apply insert_singleton).
        rewrite <- (assoc_L (∪) _ hτ1), (map_union_comm hτ1); last done.
        rewrite (assoc_L (∪)), <- (assoc_L (∪) _ hτ1).
        repeat apply map_disjoint_union_l in Hdisj as [Hdisj].
        do 2 eexists. repeat split; first by
          rewrite map_disjoint_union_r, 2 map_disjoint_union_l;
          by repeat split; try rewrite map_disjoint_singleton_l in *.
        rewrite hiter_singleton. do 3 eexists.
        split; first done.
        split.
        { 
          apply map_disjoint_singleton_l in H0.
          by apply map_disjoint_singleton_l.
        }
        
        repeat (split; last done). unfold bupdate.
        apply lookup_union_Some_inv_l in H3; last by eapply map_disjoint_singleton_l.
        apply lookup_union_Some_inv_l in H3; last by eapply map_disjoint_singleton_l.
        apply lookup_union_Some_inv_l in H3; last by eapply map_disjoint_singleton_l.
        apply lookup_singleton_Some in H3 as [_ Heq].
        inversion Heq; subst.
        by replace {[l.2 := HVal v; l.2 := HVal prev]}
          with ({[l.2 := HVal v]} : block_heap)
          by (symmetry; apply insert_singleton).
      * apply own_uninit in Hl as [? [prev ->]]. unfold hstore.
        rewrite (insert_union_l _ htrue), (insert_union_l _ hτ2).
        replace (<[l.1 := BVal sz (bupdate bh l.2 v)]> ({[l.1 := BVal 1 {[l.2 := prev]}]}))
          with ({[l.1 := BVal sz (bupdate bh l.2 v)]} : heap) by (symmetry; apply insert_singleton).
        repeat apply map_disjoint_union_l in Hdisj as [Hdisj].
        do 2 eexists. repeat split; 
          first by rewrite map_disjoint_union_l;
          split; first rewrite map_disjoint_singleton_l in *.
        rewrite hiter_singleton. do 3 eexists.
        split; first done.
        split.
        { 
          apply map_disjoint_singleton_l in Hdisj2.
          by apply map_disjoint_singleton_l.
        }
        
        repeat (split; last done). unfold bupdate.
        apply lookup_union_Some_inv_l in H3; last by eapply map_disjoint_singleton_l.
        apply lookup_union_Some_inv_l in H3; last by eapply map_disjoint_singleton_l.
        apply lookup_singleton_Some in H3 as [_ Heq].
        inversion Heq; subst.
        by replace {[l.2 := HVal v; l.2 := prev]}
          with ({[l.2 := HVal v]} : block_heap)
          by (symmetry; apply insert_singleton).
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_cons in H𝕋. destruct H𝕋 as [hl [hτ [-> [Hdisj' [Hl _]]]]].
      apply own_loc in Hl as [? [hv HSome]].
      assert (hl !! l.1 = Some Freed); last congruence.
      rewrite <- (lookup_union_l hl hτ), <- (lookup_union_l _ htrue); first done;
        first apply map_disjoint_union_l in Hdisj as [];
        by eapply (map_disjoint_Some_l hl).
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_cons in H𝕋. destruct H𝕋 as [hl [hτ [-> [Hdisj' [Hl _]]]]].
      apply own_loc in Hl as [? [hv HSome]].
      assert (l.1 ∉ dom (hl ∪ hτ ∪ htrue)) as Hfalse by assumption.
      exfalso. apply Hfalse, elem_of_dom. eexists.
      by repeat apply lookup_union_Some_l.
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_cons in H𝕋. destruct H𝕋 as [hl [hτ [-> [Hdisj' [Hl _]]]]].
      apply own_loc in Hl as [? [hv HSome]].
      apply map_disjoint_union_l in Hdisj as [].
      assert ((hl ∪ hτ ∪ htrue) !! l.1 = Some (BVal sz bh))
        as Hfalse%lookup_union_Some_inv_l%lookup_union_Some_inv_l by assumption;
        try by eapply (map_disjoint_Some_l hl).
      replace (hl !! l.1) with (Some (BVal sz bh)) in HSome by done.
      inversion HSome; subst.
      exfalso. apply H7, elem_of_dom. eexists.
      apply lookup_singleton.
  + destruct H𝕋 as [h𝕋 [htrue [-> [Hdisj [H𝕋 Htrue]]]]].
    inversion Hstep; subst.
    - eexists. split; first done.
      replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_singleton in H𝕋. destruct H𝕋 as
        [? [hl [hτ [-> [Hdisj' [[->] Hτ]]]]]].
      do 2 eexists. repeat split; first done.
      rewrite hiter_cons, (map_union_comm _ hτ); last done. do 2 eexists.
      apply map_disjoint_union_l in Hdisj as [].
      assert (({[l.1 := BVal 1 {[l.2 := HVal x]}]} ∪ hτ ∪ htrue) !! l.1 = Some (BVal sz bh))
        as Hfalse%lookup_union_Some_inv_l%lookup_union_Some_inv_l by assumption;
        try by eapply map_disjoint_singleton_l.
      apply lookup_singleton_Some in Hfalse as [_ Heq].
      repeat split; first done.
      * inversion Heq; subst; clear Heq.
        apply lookup_singleton_Some in H4 as [? Heq].
        by inversion Heq; subst.
      * rewrite hiter_singleton. right. by eexists.
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_singleton in H𝕋. destruct H𝕋 as
        [? [hl [hτ [-> [Hdisj' [[->] Hτ]]]]]].
      apply map_disjoint_union_l in Hdisj as [].
      assert (({[l.1 := BVal 1 {[l.2 := HVal x]}]} ∪ hτ ∪ htrue) !! l.1 = Some Freed)
        as Hfalse%lookup_union_Some_inv_l%lookup_union_Some_inv_l by assumption;
        try by eapply map_disjoint_singleton_l.
      apply lookup_singleton_Some in Hfalse as []. congruence.
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_singleton in H𝕋. destruct H𝕋 as
        [v' [hl [hτ [-> [Hdisj' [[->] Hτ]]]]]].
      apply map_disjoint_union_l in Hdisj as [].
      assert (({[l.1 := BVal 1 {[l.2 := HVal v']}]} ∪ hτ ∪ htrue) !! l.1 = Some (BVal sz bh))
        as Hfalse%lookup_union_Some_inv_l%lookup_union_Some_inv_l by assumption;
        try by eapply map_disjoint_singleton_l.
      apply lookup_singleton_Some in Hfalse as [? Hfalse].
      inversion Hfalse; subst.
      by apply lookup_singleton_Some in H4 as [].
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_singleton in H𝕋. destruct H𝕋 as
        [v' [hl [hτ [-> [Hdisj' [[->] Hτ]]]]]].
      apply map_disjoint_union_l in Hdisj as [].
      assert (l.1 ∉ dom ({[l.1 := BVal 1 {[l.2 := HVal v']}]} ∪ hτ ∪ htrue)) as Hfalse by assumption.
      exfalso. apply Hfalse, elem_of_dom. eexists.
      apply lookup_union_Some_l, lookup_union_Some_l, lookup_singleton.
    - replace vl with (VLoc l) in * by (simpl in *; congruence).
      rewrite hiter_singleton in H𝕋. destruct H𝕋 as
        [v' [hl [hτ [-> [Hdisj' [[->] Hτ]]]]]].
      apply map_disjoint_union_l in Hdisj as [].
      assert (({[l.1 := BVal 1 {[l.2 := HVal v']}]} ∪ hτ ∪ htrue) !! l.1 = Some (BVal sz bh))
        as Hfalse%lookup_union_Some_inv_l%lookup_union_Some_inv_l by assumption;
        try by eapply map_disjoint_singleton_l.
      apply lookup_singleton_Some in Hfalse as [? Hfalse].
      inversion Hfalse; subst.
      exfalso. apply H4, elem_of_dom. eexists.
      apply lookup_singleton.
  + destruct H𝕋 as [h𝕋𝕍 [htrue [-> [Hdisj [H𝕋𝕍 Htrue]]]]].
    apply hiter_app in H𝕋𝕍 as [h𝕋 [h𝕍 [-> [Hdisj𝕋 [H𝕋%own_typings H𝕍]]]]].
    apply map_disjoint_union_l in Hdisj as [].
    assert (h𝕋 ##ₘ h𝕍 ∪ htrue) as Hdisj by by apply map_disjoint_union_r.
    rewrite <- (assoc_L (∪)) in Hstep.
    specialize (frame_subtraction _ _ _ _ _ Hstep _ _ _ _ eq_refl Hdisj
      (map_union_id_r _) (map_disjoint_empty_r _))
      as [h𝕌' [Hdisj𝕌' [[Hstep' ->]|[m [Hstep' Hmiss]]]]].
    - specialize (IHrule _ Hval _ H𝕋 _ _ Hstep') as
        [? [-> [h𝕌 [htrue' [-> [Hdisj𝕌 [H𝕌 Htrue']]]]]]].
      apply map_disjoint_union_l in Hdisj𝕌' as [Hdisj𝕌' Hdisj'].
      apply map_disjoint_union_r in Hdisj' as [].
      apply map_disjoint_union_r in Hdisj𝕌' as [].
      rewrite (assoc_L (∪)), <- (assoc_L (∪) h𝕌), (map_union_comm _ h𝕍); last done.
      rewrite (assoc_L (∪)), <- (assoc_L (∪) _ _ htrue).
      eexists. split; first done. do 2 eexists. repeat split;
        first by rewrite map_disjoint_union_l, 2 map_disjoint_union_r.
      rewrite hiter_app. by do 2 eexists.
    - by specialize (IHrule _ Hval _ H𝕋 _ _ Hstep') as
        [? [Hfalse [h𝕌 [htrue' [-> [Hdisj𝕌 [H𝕌 Htrue']]]]]]].
  + destruct H𝕋 as [h𝕋 [htrue [-> [Hdisj [H𝕋 Htrue]]]]].
    eapply hiter_submseteq in H𝕋 as [h𝕋' [h [-> [Hdisj𝕋 H𝕋'%own_typings]]]]; last done.
    rewrite <- (assoc_L (∪)) in Hstep.
    assert (h𝕋' ##ₘ h ∪ htrue) as Hdisj' by
      by apply map_disjoint_union_l in Hdisj as []; apply map_disjoint_union_r.
    specialize (frame_subtraction _ _ _ _ _ Hstep _ _ _ _ eq_refl Hdisj'
      (map_union_id_r _) (map_disjoint_empty_r _))
      as [h𝕌'' [Hdisj𝕌'' [[Hstep' ->]|[m [Hstep' Hmiss]]]]].
    - specialize (IHrule _ Hval _ H𝕋' _ _ Hstep') as
        [? [-> [h𝕌' [htrue' [-> [Hdisj𝕌' [H𝕌' Htrue']]]]]]].
      assert (∀ v, λ𝕌 v ⊆+ λ𝕌' v) as Hsub by assumption.
      eapply hiter_submseteq in H𝕌' as [h𝕌 [? [-> [Hdisj𝕌 H𝕌]]]]; last by eapply Hsub.
      apply map_disjoint_union_l in Hdisj𝕌' as [].
      repeat apply map_disjoint_union_l in Hdisj𝕌'' as [Hdisj𝕌'' ?].
      rewrite <- 2 (assoc_L (∪) h𝕌).
      eexists. split; first done. do 2 eexists. by repeat split;
        first rewrite 2 map_disjoint_union_r.
    - by specialize (IHrule _ Hval _ H𝕋' _ _ Hstep') as
        [? [Hfalse [h𝕌' [htrue' [-> [Hdisj𝕌' [H𝕌' Htrue']]]]]]].
  + inversion Hstep; subst.
    - specialize (Hval _ _ _ H vs) as [? [? [Hsome' Hox]]].
      assert (γ !! f = Some { (xs) e}) as Hsome by assumption.
      rewrite Hsome' in Hsome; inversion Hsome; subst.
      by eapply Hox.
    - specialize (Hval _ _ _ H vs) as [xs [e [Hsome _]]].
      by rewrite Hsome in *.
Qed.
