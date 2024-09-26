From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.
From RUXt.lang Require Import semantics.
From RUXt.assertion Require Export hprop.


(*** Under-approximate specifications ***)

(* Function specifications *)
Record fun_spec := mk_fun_spec { vals : list val; pre : asrt; tag : exit; post : asrt }.
Notation "⌈ ( vs ) P | ε , Q ⌉" := (mk_fun_spec vs P ε Q).
Definition spec_ctx := gmap string (list fun_spec).
(* Context updates *)
Notation update spec f Γ := (alter (cons spec) f Γ).
(* Subset relation *)
Definition spec_ctx_subseteq (Γ Γ' : spec_ctx) : Prop :=
  ∀ f s, Γ !! f = Some s → ∃ s', Γ' !! f = Some s' ∧ s ⊆+ s'.
Notation "Γ [⊆] Γ'" := (spec_ctx_subseteq Γ Γ') (at level 50).
(* Properties *)
Lemma spec_ctx_subseteq_update Γ f spec :
  Γ [⊆] update spec f Γ.
Proof.
  intros f' s Hsome. destruct (decide (f = f')) as [->|].
  + exists (spec :: s). 
    split.
    - rewrite (lookup_alter _ Γ). by replace (Γ !! f') with (Some s).
    - rewrite submseteq_cons_r. by left.
  + exists s. split; last done.
    by rewrite (lookup_alter_ne _ Γ).
Qed.

(* Proof rules *)
Reserved Notation "Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉" (at level 50).
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
| S_Loop Γ e P Q ε :
  Γ ⊢ ⌈ P ⌉ Let <> e (Loop e) ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Loop e ⌈ ε, Q ⌉
| S_LoopCut Γ e P :
  Γ ⊢ ⌈ P ⌉ Loop e ⌈ Ok VUnit, P ⌉
| S_Alloc Γ l :
  Γ ⊢ ⌈ EMP ⌉ Alloc ⌈ Ok (VLoc l), l ↦? ⌉
| S_Free Γ l v :
  Γ ⊢ ⌈ l ↦ v ⌉ Free (TLoc l) ⌈ Ok VUnit, l ↦∅ ⌉
| S_FreeUninit Γ l :
  Γ ⊢ ⌈ l ↦? ⌉ Free (TLoc l) ⌈ Ok VUnit, l ↦∅ ⌉
| S_FreeFreed Γ l :
  Γ ⊢ ⌈ l ↦∅ ⌉ Free (TLoc l) ⌈ Err ECrash, l ↦∅ ⌉
| S_Store Γ l v v' :
  Γ ⊢ ⌈ l ↦ v' ⌉ Store (TLoc l) (TVal v) ⌈ Ok VUnit, l ↦ v ⌉
| S_StoreUninit Γ l v :
  Γ ⊢ ⌈ l ↦? ⌉ Store (TLoc l) (TVal v) ⌈ Ok VUnit, l ↦ v ⌉
| S_StoreFreed Γ l v :
  Γ ⊢ ⌈ l ↦∅ ⌉ Store (TLoc l) (TVal v) ⌈ Err ECrash, l ↦∅ ⌉
| S_Load Γ l v :
  Γ ⊢ ⌈ l ↦ v ⌉ Load (TLoc l) ⌈ Ok v, l ↦ v ⌉
| S_LoadUninit Γ l :
  Γ ⊢ ⌈ l ↦? ⌉ Load (TLoc l) ⌈ Err ECrash, l ↦? ⌉
| S_LoadFreed Γ l :
  Γ ⊢ ⌈ l ↦∅ ⌉ Load (TLoc l) ⌈ Err ECrash, l ↦∅ ⌉
| S_Frame  Γ e P Q R ε :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ⌉ →
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
Lemma S_Cons_update Γ e P Q ε f spec :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉ → update spec f Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉.
Proof.
  eapply S_Cons; first apply spec_ctx_subseteq_update. all: by intros ??.
Qed.
Lemma S_AssumeFalse Γ P ε Q :
  Γ ⊢ ⌈ P ⌉ Assume TFalse ⌈ ε, Q ⌉ → False.
Proof.
  set (e := Assume TFalse). assert (e = Assume TFalse) as Heq by done.
  intros rule; induction rule; inversion Heq.
  all: try by apply IHrule. by apply IHrule1.
Qed.

(* Environment validity *)
Reserved Notation "γ ≺ₛ Γ" (at level 50).
Inductive ux_env_rule : impl_ctx → spec_ctx → Prop :=
| S_Empty :
  ∅ ≺ₛ ∅
| S_Imp γ γ' Γ Γ' f xs e :
  γ ≺ₛ Γ → f ∉ dom γ →
  γ' = <[f := {(xs) e}]>γ → Γ' = <[f := []]>Γ →
  γ' ≺ₛ Γ'
| S_Spec γ Γ Γ' P Q ε f xs e vs :
  γ ≺ₛ Γ → γ !! f = Some {(xs) e} →
  Γ ⊢ ⌈ P ⌉ e⌊vs[//]xs⌋ ⌈ ε , Q ⌉ →
  Γ' = update ⌈(vs) P | ε, Q⌉ f Γ →
  γ ≺ₛ Γ'
where "γ ≺ₛ Γ" := (ux_env_rule γ Γ).


(*** Soundness ***)

(* Proof rule definition *)
Definition ux_frameable (ε : exit) : Prop :=
  match ε with Ok _ | Err _ => True | Miss _ => False end.
Definition ux_triple (γ : impl_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  ux_frameable ε ∧ ∀ h', hprop h' Q →
  ∃ h, hprop h P ∧ γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩.
Definition valid_specs (γ : impl_ctx) (Γ : spec_ctx) : Prop :=
  ∀ f s, Γ !! f = Some s → ∀ vs P Q ε, ⌈(vs) P | ε, Q⌉ ∈ s →
  ∃ xs e, γ !! f = Some {(xs) e} ∧ ux_triple γ (e⌊vs[//]xs⌋) P Q ε.
Definition ux_spec (Γ : spec_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  ∀ γ, valid_specs γ Γ → ux_triple γ e P Q ε.
(* Properties *)
Lemma env_inclusion (γ : impl_ctx) (Γ Γ' : spec_ctx) :
  valid_specs γ Γ → Γ' [⊆] Γ → valid_specs γ Γ'.
Proof.
  intros Hval Hsub f s' Hsome' vs P Q ε Hin'.
  specialize (Hsub _ _ Hsome') as [s [Hsome Hsub]].
  by eapply Hval; last eapply elem_of_submseteq.
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
  + apply IHrule in Hval as [Hε Hux].
    split; first done. intros h' HQ.
    apply Hux in HQ as [h [HP Hstep]].
    eexists. by split; last apply O_Loop.
  + split; first done. intros h' HQ.
    eexists. by split; last apply O_LoopCut.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. by split; last apply O_Alloc.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by do 2 eexists.
    replace {[l := Freed]} with (<[l := Freed]>{[l := LangVal v]} : heap)
      by (subst; eapply insert_singleton).
    by eapply O_Free; first done; first apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by do 2 eexists.
    replace {[l := Freed]} with (<[l := Freed]>{[l := Poison]} : heap)
      by (subst; eapply insert_singleton).
    by eapply O_Free; first done; first apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by eexists.
    by eapply O_FreeErr; first done; first apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by do 2 eexists.
    replace {[l := LangVal v]} with (<[l := LangVal v]>{[l := LangVal v']} : heap)
      by (subst; eapply insert_singleton).
    by eapply O_Store; first done; first apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by do 2 eexists.
    replace {[l := LangVal v]} with (<[l := LangVal v]>{[l := Poison]} : heap)
      by (subst; eapply insert_singleton).
    by eapply O_Store; first done; first apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by eexists.
    by eapply O_StoreErr; first done; first apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by do 2 eexists.
    by eapply O_Load; first done; first apply lookup_insert.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by eexists.
    by eapply O_LoadErr; first done; first apply lookup_insert; last right.
  + split; first done. intros h' HQ. simpl in HQ; subst.
    eexists. split; first by eexists.
    by eapply O_LoadErr; first done; first apply lookup_insert; last left.
  + apply IHrule in Hval as [Hε Hux].
    split; first done. intros h' [hQ [hR [-> [Hdisj [HQ HR]]]]].
    apply Hux in HQ as [h [HP Hstep]].
    eapply frame_addition in Hstep as [[]|[? [->]]]; last apply map_disjoint_empty_r; try done.
    eexists. by split; first do 2 eexists; last rewrite <- (map_union_empty γ).
  + specialize (IHrule1 _ Hval) as [_ Hux1]. specialize (IHrule2 _ Hval) as [Hε Hux2].
    split; first done. intros h' [HQ1|HQ2].
    - specialize (Hux1 _ HQ1) as [h1 [HP1 Hstep1]].
      eexists. by split; first left.
    - specialize (Hux2 _ HQ2) as [h2 [HP2 Hstep2]].
      eexists. by split; first right.
  + eapply env_inclusion in Hval; last done.
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
(* Soundness of environment validity *)
Theorem env_soundness γ Γ :
  γ ≺ₛ Γ → valid_specs γ Γ.
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
    eapply frame_addition in Hstep as [[]|[? [->]]]; try done; first apply map_disjoint_empty_r.
    by apply map_disjoint_singleton_r, not_elem_of_dom.
  + intros f' s HΓsome vs' P' Q' ε' Hin.
    apply lookup_alter_Some in HΓsome as [[<- [? [? ->]]]|[]]; last by eapply IHrule.
    assert (Γ ⊢ ⌈ P ⌉ e⌊vs[//]xs⌋ ⌈ ε, Q ⌉) as Hrule by assumption.    
    specialize (ux_soundness _ _ _ _ _ Hrule _ IHrule) as Hux.
    apply elem_of_cons in Hin as [Heq|]; last by eapply IHrule.
    inversion Heq; subst. by do 2 eexists.
Qed.
