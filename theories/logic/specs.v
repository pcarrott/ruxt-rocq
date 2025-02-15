From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.
From RUXt.lang Require Import semantics.
From RUXt.assertion Require Export hprop.


(*** Under-approximate specifications ***)

(* Function specifications *)
Record fun_spec := mk_fun_spec { vals : list val; pre : asrt; tag : exit; post : asrt }.
Notation "⌈ ( vs ) P | ε , Q ⌉" := (mk_fun_spec vs P ε Q).
Definition spec_ctx := gmap string (list fun_spec).
(* Overloading definitions *)
Definition empty (γ : impl_ctx) : spec_ctx := (λ _, []) <$> γ.
Definition update spec f (Γ : spec_ctx) := (alter (cons spec) f Γ).
Definition subseteq (Γ Γ' : spec_ctx) : Prop :=
  ∀ f s, Γ !! f = Some s → ∃ s', Γ' !! f = Some s' ∧ s ⊆ s'.
Notation "Γ [⊆] Γ'" := (subseteq Γ Γ') (at level 50).
Definition union (Γ1 Γ2 : spec_ctx) :=
  let f := λ s1 s2,
    match s1, s2 with
    | Some s1, Some s2 => Some (s1 ++ s2)
    | Some s, None | None, Some s => Some s
    | None, None => None
    end
  in
  merge f Γ1 Γ2.
Notation "Γ1 [∪] Γ2" := (union Γ1 Γ2) (at level 50).
(* Properties *)
Lemma spec_ctx_lookup_union_app Γ1 Γ2 f s1 s2 :
  Γ1 !! f = Some s1 → Γ2 !! f = Some s2 → (Γ1 [∪] Γ2) !! f = Some (s1 ++ s2).
Proof.
Admitted.
Lemma spec_ctx_lookup_union_l Γ1 Γ2 f s :
  (Γ1 [∪] Γ2) !! f = Some s → Γ2 !! f = None → Γ1 !! f = Some s.
Proof.
Admitted.
Lemma spec_ctx_lookup_union_r Γ1 Γ2 f s :
  (Γ1 [∪] Γ2) !! f = Some s → Γ1 !! f = None → Γ2 !! f = Some s.
Proof.
Admitted.
Lemma spec_ctx_subseteq_refl Γ : Γ [⊆] Γ.
Proof.
Admitted.
Lemma spec_ctx_subseteq_union_r Γ1 Γ2 : Γ1 [⊆] (Γ1 [∪] Γ2).
Proof.
Admitted.
Lemma spec_ctx_subseteq_union_l Γ1 Γ2 : Γ1 [⊆] (Γ2 [∪] Γ1).
Proof.
Admitted.

(* Proof rules *)
Definition ux_frameable (ε : exit) (R : asrt) : Prop :=
  match ε with Miss (MLoc l) => ∀ h, hprop h R → l.1 ∉ dom h | _ => True end.
Reserved Notation "Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉".
Inductive ux_rule : spec_ctx → asrt → expr → exit → asrt → Prop :=
| S_Value Γ v :
  Γ ⊢ ⌈ EMP ⌉ Pure (PVal v) ⌈ Ok v, EMP ⌉
| S_Minus Γ p z :
  Γ ⊢ ⌈ EMP ⌉ Pure p ⌈ Ok (VInt z), EMP ⌉ →
  Γ ⊢ ⌈ EMP ⌉ Pure (PMinus p) ⌈ Ok (VInt (-z)), EMP ⌉
| S_Not Γ p b :
  Γ ⊢ ⌈ EMP ⌉ Pure p ⌈ Ok (VBool b), EMP ⌉ →
  Γ ⊢ ⌈ EMP ⌉ Pure (PNot p) ⌈ Ok (VBool (negb b)), EMP ⌉
| S_Add Γ p1 p2 z1 z2 :
  Γ ⊢ ⌈ EMP ⌉ Pure p1 ⌈ Ok (VInt z1), EMP ⌉ → Γ ⊢ ⌈ EMP ⌉ Pure p2 ⌈ Ok (VInt z2), EMP ⌉ →
  Γ ⊢ ⌈ EMP ⌉ Pure (PAdd p1 p2) ⌈ Ok (VInt (z1 + z2)), EMP ⌉
| S_Le Γ p1 p2 z1 z2 :
  Γ ⊢ ⌈ EMP ⌉ Pure p1 ⌈ Ok (VInt z1), EMP ⌉ → Γ ⊢ ⌈ EMP ⌉ Pure p2 ⌈ Ok (VInt z2), EMP ⌉ →
  Γ ⊢ ⌈ EMP ⌉ Pure (PLe p1 p2) ⌈ Ok (VBool (Z.leb z1 z2)), EMP ⌉
| S_Assume Γ :
  Γ ⊢ ⌈ EMP ⌉ Assume TTrue ⌈ Ok VUnit, EMP ⌉
| S_Error Γ :
  Γ ⊢ ⌈ EMP ⌉ Error ⌈ Err ECrash, EMP ⌉
| S_Let Γ x e1 e2 P Q R v ε :
  Γ ⊢ ⌈ P ⌉ e1 ⌈ Ok v, R ⌉ → Γ ⊢ ⌈ R ⌉ e2⌊v//x⌋ ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Let x e1 e2 ⌈ ε, Q ⌉
| S_LetCut Γ x e1 e2 P Q ξ :
  Γ ⊢ ⌈ P ⌉ e1 ⌈ Err ξ, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Let x e1 e2 ⌈ Err ξ, Q ⌉
| S_Choice Γ ei e1 e2 P Q ε :
  Γ ⊢ ⌈ P ⌉ ei ⌈ ε, Q ⌉ → (ei = e1 ∨ ei = e2) →
  Γ ⊢ ⌈ P ⌉ Choice e1 e2 ⌈ ε, Q ⌉
| S_Alloc Γ l :
  Γ ⊢ ⌈ EMP ⌉ Alloc (TInt 1) ⌈ Ok (VLoc l), l ↦? ⌉
| S_Free Γ l v :
  Γ ⊢ ⌈ l ↦ v ⌉ Free (TLoc l) ⌈ Ok VUnit, l ↦∅ ⌉
| S_FreeUninit Γ l :
  Γ ⊢ ⌈ l ↦? ⌉ Free (TLoc l) ⌈ Ok VUnit, l ↦∅ ⌉
| S_FreeFreed Γ l :
  Γ ⊢ ⌈ l ↦∅ ⌉ Free (TLoc l) ⌈ Err ECrash, l ↦∅ ⌉
| S_FreeEmp Γ l :
  Γ ⊢ ⌈ EMP ⌉ Free (TLoc l) ⌈ Miss (MLoc l), EMP ⌉
| S_Store Γ l v v' :
  Γ ⊢ ⌈ l ↦ v' ⌉ Store (TLoc l) (TVal v) ⌈ Ok VUnit, l ↦ v ⌉
| S_StoreUninit Γ l v :
  Γ ⊢ ⌈ l ↦? ⌉ Store (TLoc l) (TVal v) ⌈ Ok VUnit, l ↦ v ⌉
| S_StoreFreed Γ l v :
  Γ ⊢ ⌈ l ↦∅ ⌉ Store (TLoc l) (TVal v) ⌈ Err ECrash, l ↦∅ ⌉
| S_StoreEmp Γ l v :
  Γ ⊢ ⌈ EMP ⌉ Store (TLoc l) (TVal v) ⌈ Miss (MLoc l), EMP ⌉
| S_Load Γ l v :
  Γ ⊢ ⌈ l ↦ v ⌉ Load (TLoc l) ⌈ Ok v, l ↦ v ⌉
| S_LoadUninit Γ l :
  Γ ⊢ ⌈ l ↦? ⌉ Load (TLoc l) ⌈ Err ECrash, l ↦? ⌉
| S_LoadFreed Γ l :
  Γ ⊢ ⌈ l ↦∅ ⌉ Load (TLoc l) ⌈ Err ECrash, l ↦∅ ⌉
| S_LoadEmp Γ l :
  Γ ⊢ ⌈ EMP ⌉ Load (TLoc l) ⌈ Miss (MLoc l), EMP ⌉
| S_Frame  Γ e P Q R ε :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ⌉ → ux_frameable ε R →
  Γ ⊢ ⌈ P ∗ R ⌉ e ⌈ ε, Q ∗ R ⌉
| S_Disj Γ e P1 P2 Q1 Q2 ε :
  Γ ⊢ ⌈ P1 ⌉ e ⌈ ε, Q1 ⌉ → Γ ⊢ ⌈ P2 ⌉ e ⌈ ε, Q2 ⌉ →
  Γ ⊢ ⌈ P1 ∨ₕ P2 ⌉ e ⌈ ε, Q1 ∨ₕ Q2 ⌉
| S_Cons Γ Γ' e P P' Q Q' ε :
  Γ' [⊆] Γ → (⊨ (P' →ₕ P)) → (⊨ (Q →ₕ Q')) → Γ' ⊢ ⌈ P' ⌉ e ⌈ ε , Q' ⌉ →
  Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉
| S_Exists Γ e P Q ε X :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ ∃ₕ x ⋮ X, P ⌉ e ⌈ ε, ∃ₕ x ⋮ X, Q ⌉
| S_Call Γ f ts vs P Q ε s :
  Γ !! f = Some s → ⌈(vs) P | ε, Q⌉ ∈ s → ts = TVals vs →
  Γ ⊢ ⌈ P ⌉ Call f ts ⌈ ε , Q ⌉
where "Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉" := (ux_rule Γ P e ε Q).
(* Derived rules *)
Lemma S_EnvUnionL Γ1 Γ2 e P Q ε :
  Γ1 ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉ → (Γ1 [∪] Γ2) ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉.
Proof.
  intros Hrule. eapply S_Cons; last done.
  + eapply spec_ctx_subseteq_union_r.
  + apply himplies_refl.
  + apply himplies_refl.
Qed.
Lemma S_EnvUnionR Γ1 Γ2 e P Q ε :
  Γ2 ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉ → (Γ1 [∪] Γ2) ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉.
Proof.
  intros Hrule. eapply S_Cons; last done.
  + eapply spec_ctx_subseteq_union_l.
  + apply himplies_refl.
  + apply himplies_refl.
Qed.
Lemma S_FrameEmpL Γ e P Q ε :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ⌉ ↔ Γ ⊢ ⌈ P ∗ EMP ⌉ e ⌈ ε, Q ⌉.
Proof.
  split; intros Hrule.
  + eapply S_Cons; last done.
    - apply spec_ctx_subseteq_refl.
    - apply hempty_right.
    - apply himplies_refl.
  + eapply S_Cons; last done.
    - apply spec_ctx_subseteq_refl.
    - apply hempty_left.
    - apply himplies_refl.
Qed.
Lemma S_FrameEmpR Γ e P Q ε :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ⌉ ↔ Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ∗ EMP ⌉.
Proof.
  split; intros Hrule.
  + eapply S_Cons; last done.
    - apply spec_ctx_subseteq_refl.
    - apply himplies_refl.
    - apply hempty_left.
  + eapply S_Cons; last done.
    - apply spec_ctx_subseteq_refl.
    - apply himplies_refl.
    - apply hempty_right.
Qed.
Lemma S_CommPre Γ e P Q R ε :
  Γ ⊢ ⌈ P ∗ R ⌉ e ⌈ ε, Q ⌉ ↔ Γ ⊢ ⌈ R ∗ P ⌉ e ⌈ ε, Q ⌉.
Proof.
  split; intros Hrule.
  + eapply S_Cons; last done.
    - apply spec_ctx_subseteq_refl.
    - intros h HPR. by apply hstar_comm.
    - apply himplies_refl.
  + eapply S_Cons; last done.
    - apply spec_ctx_subseteq_refl.
    - intros h HRP. by apply hstar_comm.
    - apply himplies_refl.
Qed.
Lemma S_CommPost Γ e P Q R ε :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ∗ R ⌉ ↔ Γ ⊢ ⌈ P ⌉ e ⌈ ε, R ∗ Q ⌉.
Proof.
  split; intros Hrule.
  + eapply S_Cons; last done.
    - apply spec_ctx_subseteq_refl.
    - apply himplies_refl.
    - intros h HRQ. by apply hstar_comm.
  + eapply S_Cons; last done.
    - apply spec_ctx_subseteq_refl.
    - apply himplies_refl.
    - intros h HQR. by apply hstar_comm.
Qed.

(* Well-formed specification contexts *)
Reserved Notation "γ ≺ₛ Γ" (at level 50).
Inductive wf_spec_ctx : impl_ctx → spec_ctx → Prop :=
| E_Empty :
  ∅ ≺ₛ ∅
| E_Imp γ γ' Γ Γ' f xs e :
  γ ≺ₛ Γ → f ∉ dom γ →
  γ' = <[f := {(xs) e}]>γ → Γ' = <[f := []]>Γ →
  γ' ≺ₛ Γ'
| E_Spec γ Γ Γ' P Q ε f xs e vs :
  γ ≺ₛ Γ → γ !! f = Some {(xs) e} →
  Γ ⊢ ⌈ P ⌉ e⌊vs[//]xs⌋ ⌈ ε , Q ⌉ →
  Γ' = update ⌈(vs) P | ε, Q⌉ f Γ →
  γ ≺ₛ Γ'
| E_Union γ Γ1 Γ2 :
  γ ≺ₛ Γ1 → γ ≺ₛ Γ2 → γ ≺ₛ (Γ1 [∪] Γ2)
where "γ ≺ₛ Γ" := (wf_spec_ctx γ Γ).
(* Derive rules *)
Lemma wf_empty_spec_ctx γ : γ ≺ₛ empty γ.
Proof.
  generalize γ. apply map_ind.
  + apply E_Empty.
  + intros f [] γ' HNone Henv.
    eapply E_Imp; try done.
    - by apply not_elem_of_dom.
    - unfold empty; by rewrite fmap_insert.
Qed.
(* Well-formed function specifications *)
Definition wf_fun_spec (γ : impl_ctx) f vs P Q ε :=
  ∃ Γ s, γ ≺ₛ Γ ∧ Γ !! f = Some s ∧ ⌈(vs) P | ε, Q⌉ ∈ s.


(*** Soundness ***)

(* Proof rule definition *)
Definition valid_exit (ε : exit) : Prop :=
  match ε with Miss (MFun _) => False | _ => True end.
Definition ux_triple (γ : impl_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  valid_exit ε ∧ ∀ h', hprop h' Q →
  ∃ h, hprop h P ∧ γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩.
Definition valid_fun_spec (γ : impl_ctx) f vs P Q ε :=
  ∃ xs e, γ !! f = Some {(xs) e} ∧ ux_triple γ (e⌊vs[//]xs⌋) P Q ε.
Definition valid_spec_ctx (γ : impl_ctx) (Γ : spec_ctx) : Prop :=
  ∀ f s, Γ !! f = Some s → ∀ vs P Q ε, ⌈(vs) P | ε, Q⌉ ∈ s →
  valid_fun_spec γ f vs P Q ε.
Definition ux_spec (Γ : spec_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  ∀ γ, valid_spec_ctx γ Γ → ux_triple γ e P Q ε.
(* Properties *)
Lemma spec_ctx_inclusion (γ : impl_ctx) (Γ Γ' : spec_ctx) :
  valid_spec_ctx γ Γ → Γ' [⊆] Γ → valid_spec_ctx γ Γ'.
Proof.
  intros Hval Hsub f s' Hsome' vs P Q ε Hin'.
  specialize (Hsub _ _ Hsome') as [s [Hsome Hsub]].
  by eapply Hval; last eapply elem_of_subseteq.
Qed.

(* Soundness of proof rules *)
Theorem ux_soundness Γ P e ε Q :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉ → ux_spec Γ e P Q ε.
Proof.
  intros rule; induction rule; intros γ Hval.
  + split; first done. intros h' HQ.
    eexists. by split; last apply O_Pure.
  + apply IHrule in Hval as [_ Hux].
    split; first done. intros h' HQ.
    apply Hux in HQ as [h [HP Hstep]].
    eexists. by split; last (inversion Hstep; apply O_Pure, pure_neg_Some).
  + apply IHrule in Hval as [_ Hux].
    split; first done. intros h' HQ.
    apply Hux in HQ as [h [HP Hstep]].
    eexists. by split; last (inversion Hstep; apply O_Pure, pure_not_Some).
  + specialize (IHrule1 _ Hval) as [_ Hux1]. specialize (IHrule2 _ Hval) as [_ Hux2].
    split; first done. intros h' HQ.
    specialize (Hux1 _ HQ) as [h1 [HP1 Hstep1]]. specialize (Hux2 _ HQ) as [h2 [HP2 Hstep2]].
    eexists. by split; last (inversion Hstep1; inversion Hstep2; apply O_Pure, pure_plus_Some).
  + specialize (IHrule1 _ Hval) as [_ Hux1]. specialize (IHrule2 _ Hval) as [_ Hux2].
    split; first done. intros h' HQ.
    specialize (Hux1 _ HQ) as [h1 [HP1 Hstep1]]. specialize (Hux2 _ HQ) as [h2 [HP2 Hstep2]].
    eexists. by split; last (inversion Hstep1; inversion Hstep2; apply O_Pure, pure_le_Some).
  + split; first done. intros h' HQ.
    eexists. by split; last apply O_Assume.
  + split; first done. intros h' HQ.
    eexists. by split; last apply O_Error.
  + specialize (IHrule1 _ Hval) as [_ Hux1]. specialize (IHrule2 _ Hval) as [Hε Hux2].
    split; first done. intros h' HQ.
    apply Hux2 in HQ as [h'' [HR Hstep2]]. apply Hux1 in HR as [h [HP Hstep1]].
    eexists. by split; last eapply O_Let.
  + apply IHrule in Hval as [_ Hux].
    split; first done. intros h' HQ.
    apply Hux in HQ as [h [HP Hstep]].
    eexists. by split; last apply O_LetErr.
  + apply IHrule in Hval as [Hε Hux].
    split; first done. intros h' HQ.
    apply Hux in HQ as [h [HP Hstep]].
    eexists. by split; last eapply O_Choice.
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done. rewrite Hi.
    by apply (O_Alloc _ _ _ _ _ 1).
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done.
    eapply O_Free; try done; first apply lookup_insert.
    intros. apply dom_singleton, elem_of_singleton. lia.
    unfold hupdate. symmetry. apply insert_singleton.
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done.
    eapply O_Free; try done; first apply lookup_insert.
    intros. apply dom_singleton, elem_of_singleton. lia.
    unfold hupdate. symmetry. apply insert_singleton.
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_FreeErrBlock; last apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by eexists.
    by eapply O_FreeMiss; last apply not_elem_of_dom.
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done.
    eapply O_Store; try done; try (apply elem_of_dom; eexists); try apply lookup_insert.
    unfold hupdate, bupdate. replace {[l.2 := HVal v; l.2 := HVal v']} with
      ({[l.2 := HVal v]} : block_heap); by symmetry; apply insert_singleton.
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done.
    eapply O_Store; try done; try (apply elem_of_dom; eexists); try apply lookup_insert.
    unfold hupdate, bupdate. replace {[l.2 := HVal v; l.2 := Poison]} with
      ({[l.2 := HVal v]} : block_heap); by symmetry; apply insert_singleton.
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_StoreErr; last apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first done.
    by eapply O_StoreMiss; last apply not_elem_of_dom.
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_Load; try apply lookup_insert.
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_LoadErrBlock; try apply lookup_insert.
  + split; first done. intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_LoadErr; try apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by eexists.
    by eapply O_LoadMiss; last apply not_elem_of_dom.
  + apply IHrule in Hval as [Hε Hux].
    split; first done. intros h' [hQ [hR [-> [Hdisj [HQ HR]]]]].
    apply Hux in HQ as [h [HP Hstep]].
    eapply frame_addition in Hstep as [[]|[m [-> Hmiss]]]; last apply map_disjoint_empty_r; try done.
    - eexists. by split; first do 2 eexists; last rewrite <- (map_union_empty γ).
    - exfalso. assert (ux_frameable (Miss m) R) as Hframe by assumption.
      by destruct Hmiss as [[?[->]]|[?[]]]; first apply Hframe in HR.
  + specialize (IHrule1 _ Hval) as [_ Hux1]. specialize (IHrule2 _ Hval) as [Hε Hux2].
    split; first done. intros h' [HQ1|HQ2].
    - specialize (Hux1 _ HQ1) as [h1 [HP1 Hstep1]].
      eexists. by split; first left.
    - specialize (Hux2 _ HQ2) as [h2 [HP2 Hstep2]].
      eexists. by split; first right.
  + eapply spec_ctx_inclusion in Hval; last done.
    apply IHrule in Hval as [Hε Hux].
    split; first done. intros h' HQ.
    assert (⊨ (Q →ₕ Q')) as HQimp by assumption; apply HQimp in HQ.
    apply Hux in HQ as [h [HP Hstep]].
    assert (⊨ (P' →ₕ P)) as HPimp by assumption; apply HPimp in HP.
    by eexists.
  + apply IHrule in Hval as [Hε Hux].
    split; first done. intros h' [v HQ].
    apply Hux in HQ as [h [HP Hstep]].
    eexists. by split; first by eexists.
  + assert (Γ !! f = Some s ∧ ⌈(vs) P | ε, Q⌉ ∈ s) as [HΓsome Hspec] by done.
    eapply Hval in HΓsome as [xs [e [Hγsome [Hε Hux]]]]; first done.
    split; first done. intros h' HQ.
    apply Hux in HQ as [h [HP Hstep]].
    eexists. by split; last (subst; eapply O_Call).
Qed.
(* Soundness of specification contexts *)
Theorem env_soundness γ Γ :
  γ ≺ₛ Γ → valid_spec_ctx γ Γ.
Proof.
  intros rule; induction rule; subst.
  + done.
  + intros f' s HΓsome vs P Q ε Hin.
    apply lookup_insert_Some in HΓsome as [[_ <-]|[? HΓsome]]; first inversion Hin.
    eapply IHrule in HΓsome as [xs' [e' [Hγsome [Hε Hux]]]]; first done.
    do 2 eexists. split; first by rewrite (lookup_insert_ne γ).
    split; first done. intros h' HQ.
    specialize (Hux _ HQ) as [h [HP Hstep]].
    eexists. split; first done.
    rewrite (insert_union_singleton_r γ); last by apply not_elem_of_dom.
    rewrite <- (map_union_empty h), <- (map_union_empty h').
    eapply frame_addition in Hstep as [[]|[[] [-> [[?[]]|[?[]]]]]];
      try done; first apply map_disjoint_empty_r.
    by apply map_disjoint_singleton_r, not_elem_of_dom.
  + intros f' s HΓsome vs' P' Q' ε' Hin. unfold update in HΓsome.
    apply lookup_alter_Some in HΓsome as [[<- [? [? ->]]]|[]]; last by eapply IHrule.
    assert (Γ ⊢ ⌈ P ⌉ e⌊vs[//]xs⌋ ⌈ ε, Q ⌉) as Hrule by assumption.    
    specialize (ux_soundness _ _ _ _ _ Hrule _ IHrule) as Hux.
    apply elem_of_cons in Hin as [Heq|]; last by eapply IHrule.
    inversion Heq; subst. by do 2 eexists.
  + intros f s HΓsome vs P Q ε Hin.
    unfold valid_spec_ctx in *.
    destruct (Γ1 !! f) eqn:Hopt1.
    - destruct (Γ2 !! f) eqn:Hopt2.
      * specialize (spec_ctx_lookup_union_app _ _ _ _ _ Hopt1 Hopt2) as Happ.
        replace ((Γ1 [∪] Γ2) !! f) with (Some s) in Happ. inversion Happ; subst.
        apply elem_of_app in Hin as [|].
        ++ by eapply IHrule1.
        ++ by eapply IHrule2.
      * by eapply IHrule1;
        first eapply spec_ctx_lookup_union_l.
    - by eapply IHrule2;
      first eapply spec_ctx_lookup_union_r.
Qed.
(* Soundness of well-formed function specifications *)
Theorem fun_spec_soundness γ f vs P Q ε :
  wf_fun_spec γ f vs P Q ε → valid_fun_spec γ f vs P Q ε.
Proof.
  intros [Γ [s [Himpl [HenvS Hspec]]]].
  by eapply env_soundness.
Qed.
