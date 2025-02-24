From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang semantics assertion.
From RUXt.model Require Import logic.


(*** The RISL Program Logic ***)

(* Function specifications *)
Record fun_spec := mk_fun_spec { vals : list val; pre : asrt; tag : exit; post : asrt }.
Notation "⌈ ( vs ) P | ε , Q ⌉" := (mk_fun_spec vs P ε Q).
Definition spec_ctx := gmap string (list fun_spec).
(* Overloading definitions *)
Definition empty (γ : impl_ctx) : spec_ctx := (λ _, []) <$> γ.
Definition update spec f (Γ : spec_ctx) := alter (cons spec) f Γ.
Definition subseteq (Γ Γ' : spec_ctx) : Prop :=
  ∀ f s, Γ !! f = Some s → ∃ s', Γ' !! f = Some s' ∧ s ⊆ s'.
Notation "Γ [⊆] Γ'" := (subseteq Γ Γ') (at level 50).

(* Proof rules *)
Reserved Notation "Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉".
Definition ux_frameable (ε : exit) (R : asrt) : Prop :=
  match ε with Miss l => ∀ h, hprop h R → l.1 ∉ dom h | _ => True end.
Inductive wf_spec : spec_ctx → asrt → expr → exit → asrt → Prop :=
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
  Γ ⊢ ⌈ EMP ⌉ Error ⌈ Err, EMP ⌉
| S_Let Γ x e1 e2 P Q R v ε :
  Γ ⊢ ⌈ P ⌉ e1 ⌈ Ok v, R ⌉ → Γ ⊢ ⌈ R ⌉ e2⌊v//x⌋ ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Let x e1 e2 ⌈ ε, Q ⌉
| S_LetCut Γ x e1 e2 P Q :
  Γ ⊢ ⌈ P ⌉ e1 ⌈ Err, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Let x e1 e2 ⌈ Err, Q ⌉
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
  Γ ⊢ ⌈ l ↦∅ ⌉ Free (TLoc l) ⌈ Err, l ↦∅ ⌉
| S_FreeEmp Γ l :
  Γ ⊢ ⌈ EMP ⌉ Free (TLoc l) ⌈ Miss l, EMP ⌉
| S_Store Γ l v v' :
  Γ ⊢ ⌈ l ↦ v' ⌉ Store (TLoc l) (TVal v) ⌈ Ok VUnit, l ↦ v ⌉
| S_StoreUninit Γ l v :
  Γ ⊢ ⌈ l ↦? ⌉ Store (TLoc l) (TVal v) ⌈ Ok VUnit, l ↦ v ⌉
| S_StoreFreed Γ l v :
  Γ ⊢ ⌈ l ↦∅ ⌉ Store (TLoc l) (TVal v) ⌈ Err, l ↦∅ ⌉
| S_StoreEmp Γ l v :
  Γ ⊢ ⌈ EMP ⌉ Store (TLoc l) (TVal v) ⌈ Miss l, EMP ⌉
| S_Load Γ l v :
  Γ ⊢ ⌈ l ↦ v ⌉ Load (TLoc l) ⌈ Ok v, l ↦ v ⌉
| S_LoadUninit Γ l :
  Γ ⊢ ⌈ l ↦? ⌉ Load (TLoc l) ⌈ Err, l ↦? ⌉
| S_LoadFreed Γ l :
  Γ ⊢ ⌈ l ↦∅ ⌉ Load (TLoc l) ⌈ Err, l ↦∅ ⌉
| S_LoadEmp Γ l :
  Γ ⊢ ⌈ EMP ⌉ Load (TLoc l) ⌈ Miss l, EMP ⌉
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
| S_Call Γ f vs P Q ε s :
  Γ !! f = Some s → ⌈(vs) P | ε, Q⌉ ∈ s →
  Γ ⊢ ⌈ P ⌉ Call f (TVals vs) ⌈ ε , Q ⌉
where "Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉" := (wf_spec Γ P e ε Q).

(* Well-formed specification contexts *)
Reserved Notation "γ ≺ₛ Γ" (at level 50).
Inductive wf_spec_ctx : impl_ctx → spec_ctx → Prop :=
| E_Empty γ :
  γ ≺ₛ empty γ
| E_Update γ Γ Γ' P Q ε f xs e vs :
  γ ≺ₛ Γ → γ !! f = Some {(xs) e} →
  Γ ⊢ ⌈ P ⌉ e⌊vs[//]xs⌋ ⌈ ε , Q ⌉ →
  Γ' = update ⌈(vs) P | ε, Q⌉ f Γ →
  γ ≺ₛ Γ'
where "γ ≺ₛ Γ" := (wf_spec_ctx γ Γ).


(*** Soundness ***)

(* Proof rule definition *)
Definition valid_spec_ctx (γ : impl_ctx) (Γ : spec_ctx) : Prop :=
  ∀ f s, Γ !! f = Some s → ∀ vs P Q ε, ⌈(vs) P | ε, Q⌉ ∈ s →
  ∃ xs e, γ !! f = Some {(xs) e} ∧ ux_triple γ (e⌊vs[//]xs⌋) P Q ε.
Definition valid_spec (Γ : spec_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
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
Theorem spec_soundness Γ P e ε Q :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉ → valid_spec Γ e P Q ε.
Proof.
  intros rule; induction rule; intros γ Hval.
  + intros h' HQ. eexists.
    by split; last apply O_Pure.
  + apply IHrule in Hval as Hux. intros h' HQ. 
    apply Hux in HQ as [h [HP Hstep]]. eexists.
    by split; last (inversion Hstep; apply O_Pure, pure_neg_Some).
  + apply IHrule in Hval as Hux. intros h' HQ.
    apply Hux in HQ as [h [HP Hstep]]. eexists.
    by split; last (inversion Hstep; apply O_Pure, pure_not_Some).
  + specialize (IHrule1 _ Hval) as Hux1. intros h' HQ.
    specialize (Hux1 _ HQ) as [h1 [HP1 Hstep1]].
    specialize (IHrule2 _ Hval) as Hux2. eexists.
    specialize (Hux2 _ HQ) as [h2 [HP2 Hstep2]].
    by split; last (inversion Hstep1; inversion Hstep2; apply O_Pure, pure_plus_Some).
  + specialize (IHrule1 _ Hval) as Hux1. intros h' HQ.
    specialize (Hux1 _ HQ) as [h1 [HP1 Hstep1]].
    specialize (IHrule2 _ Hval) as Hux2. eexists.
    specialize (Hux2 _ HQ) as [h2 [HP2 Hstep2]].
    by split; last (inversion Hstep1; inversion Hstep2; apply O_Pure, pure_le_Some).
  + intros h' HQ. eexists.
    by split; last apply O_Assume.
  + intros h' HQ. eexists.
    by split; last apply O_Error.
  + specialize (IHrule1 _ Hval) as Hux1. specialize (IHrule2 _ Hval) as Hux2.
    intros h' HQ. apply Hux2 in HQ as [h'' [HR Hstep2]].
    apply Hux1 in HR as [h [HP Hstep1]]. eexists.
    by split; last eapply O_Let.
  + apply IHrule in Hval as Hux. intros h' HQ.
    apply Hux in HQ as [h [HP Hstep]]. eexists.
    by split; last apply O_LetErr.
  + apply IHrule in Hval as Hux. intros h' HQ.
    apply Hux in HQ as [h [HP Hstep]]. eexists.
    by split; last eapply O_Choice.
  + intros h' [? Hi]; subst.
    eexists. split; first done. rewrite Hi.
    by apply (O_Alloc _ _ _ _ _ 1).
  + intros h' [? Hi]; subst.
    eexists. split; first done.
    eapply O_Free; try done; first apply lookup_insert.
    intros. apply dom_singleton, elem_of_singleton. lia.
    unfold hupdate. symmetry. apply insert_singleton.
  + intros h' [? Hi]; subst.
    eexists. split; first done.
    eapply O_Free; try done; first apply lookup_insert.
    intros. apply dom_singleton, elem_of_singleton. lia.
    unfold hupdate. symmetry. apply insert_singleton.
  + intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_FreeErrBlock; last apply lookup_insert.
  + intros h' HQ. simpl in HQ; subst.
    eexists. split; first by eexists.
    by eapply O_FreeMiss; last apply not_elem_of_dom.
  + intros h' [? Hi]; subst.
    eexists. split; first done.
    eapply O_Store; try done; try (apply elem_of_dom; eexists); try apply lookup_insert.
    unfold hupdate, bupdate. replace {[l.2 := HVal v; l.2 := HVal v']} with
      ({[l.2 := HVal v]} : block_heap); by symmetry; apply insert_singleton.
  + intros h' [? Hi]; subst.
    eexists. split; first done.
    eapply O_Store; try done; try (apply elem_of_dom; eexists); try apply lookup_insert.
    unfold hupdate, bupdate. replace {[l.2 := HVal v; l.2 := Poison]} with
      ({[l.2 := HVal v]} : block_heap); by symmetry; apply insert_singleton.
  + intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_StoreErr; last apply lookup_insert.
  + intros h' HQ. simpl in HQ; subst.
    eexists. split; first done.
    by eapply O_StoreMiss; last apply not_elem_of_dom.
  + intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_Load; try apply lookup_insert.
  + intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_LoadErrBlock; try apply lookup_insert.
  + intros h' [? Hi]; subst.
    eexists. split; first done.
    by eapply O_LoadErr; try apply lookup_insert.
  + intros h' HQ. simpl in HQ; subst.
    eexists. split; first by eexists.
    by eapply O_LoadMiss; last apply not_elem_of_dom.
  + apply IHrule in Hval as Hux.
    intros h' [hQ [hR [-> [Hdisj [HQ HR]]]]].
    apply Hux in HQ as [h [HP Hstep]].
    eapply frame_addition in Hstep as [[]|[l [-> Hmiss]]]; try done.
    - eexists. by split; first do 2 eexists.
    - assert (ux_frameable (Miss l) R) as Hframe by assumption.
      exfalso. by apply Hframe in HR.
  + specialize (IHrule1 _ Hval) as Hux1. specialize (IHrule2 _ Hval) as Hux2.
    intros h' [HQ1|HQ2].
    - specialize (Hux1 _ HQ1) as [h1 [HP1 Hstep1]].
      eexists. by split; first left.
    - specialize (Hux2 _ HQ2) as [h2 [HP2 Hstep2]].
      eexists. by split; first right.
  + assert (⊨ (P' →ₕ P)) as HPimp by assumption.
    assert (⊨ (Q →ₕ Q')) as HQimp by assumption.
    eapply spec_ctx_inclusion in Hval; last done.
    apply IHrule in Hval as Hux.
    intros h' [h [HP Hstep]]%HQimp%Hux.
    apply HPimp in HP. by eexists.
  + apply IHrule in Hval as Hux.
    intros h' [v [h [HP Hstep]]%Hux].
    eexists. by split; first by eexists.
  + assert (Γ !! f = Some s ∧ ⌈(vs) P | ε, Q⌉ ∈ s) as [HΓsome Hspec] by done.
    eapply Hval in HΓsome as [xs [e [Hγsome Hux]]]; first done.
    intros h' [h [HP Hstep]]%Hux.
    eexists. by split; last (subst; eapply O_Call).
Qed.

(* Soundness of specification contexts *)
Theorem spec_ctx_soundness γ Γ :
  γ ≺ₛ Γ → valid_spec_ctx γ Γ.
Proof.
  intros rule; induction rule; subst.
  + intros f s HΓsome vs P Q ε Hin.
    apply lookup_fmap_Some in HΓsome as [_[<- _]].
    exfalso. inversion Hin.
  + intros f' s HΓsome vs' P' Q' ε' Hin. unfold update in HΓsome.
    apply lookup_alter_Some in HΓsome as [[<- [? [? ->]]]|[]]; last by eapply IHrule.
    assert (Γ ⊢ ⌈ P ⌉ e⌊vs[//]xs⌋ ⌈ ε, Q ⌉) as Hrule by assumption.    
    specialize (spec_soundness _ _ _ _ _ Hrule _ IHrule) as Hux.
    apply elem_of_cons in Hin as [Heq|]; last by eapply IHrule.
    inversion Heq; subst. by do 2 eexists.
Qed.

(* Instantiate RISL for the refutation algorithm *)
Program Definition risl : logic := {|
  derivable_spec γ e P Q ε := ∃ Γ, γ ≺ₛ Γ ∧ Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉;
|}.
Next Obligation.
  intros γ e P Q ε [Γ [Hctx%spec_ctx_soundness Hspec%spec_soundness]].
  by apply Hspec.
Qed.
