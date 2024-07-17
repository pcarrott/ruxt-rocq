From RUXt.lang Require Import semantics.
From RUXt.assertion Require Export hprop.
From RUXt.lib Require Export gmap.


(*** Under-approximate specifications ***)

(* Function specifications *)
Record fun_spec := mk_fun_spec { vals : list val; pre : hprop; tag : exit; post : hprop }.
Notation "[ ( vs ) P | ε , Q ]" := (mk_fun_spec vs P ε Q).
Definition spec_ctx := gmap string (list fun_spec).

(* Proof rules *)
Reserved Notation "Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉"
  (at level 100, no associativity).
Inductive ux_rule : spec_ctx → hprop → expr → exit → hprop → Prop :=
| R_Value : ∀ Γ v,
  Γ ⊢ ⌈ emp ⌉ Pure (PVal v) ⌈ Ok v, emp ⌉
| R_Neg : ∀ Γ p z,
  Γ ⊢ ⌈ emp ⌉ Pure p ⌈ Ok (VInt z), emp ⌉ →
  Γ ⊢ ⌈ emp ⌉ Pure (PNeg p) ⌈ Ok (VInt (-z)), emp ⌉
| R_Not : ∀ Γ p b,
  Γ ⊢ ⌈ emp ⌉ Pure p ⌈ Ok (VBool b), emp ⌉ →
  Γ ⊢ ⌈ emp ⌉ Pure (PNot p) ⌈ Ok (VBool (negb b)), emp ⌉
| R_Plus : ∀ Γ p1 p2 z1 z2,
  Γ ⊢ ⌈ emp ⌉ Pure p1 ⌈ Ok (VInt z1), emp ⌉ → Γ ⊢ ⌈ emp ⌉ Pure p2 ⌈ Ok (VInt z2), emp ⌉ →
  Γ ⊢ ⌈ emp ⌉ Pure (PPlus p1 p2) ⌈ Ok (VInt (z1 + z2)), emp ⌉
| R_Eq : ∀ Γ p1 p2 z1 z2,
  Γ ⊢ ⌈ emp ⌉ Pure p1 ⌈ Ok (VInt z1), emp ⌉ → Γ ⊢ ⌈ emp ⌉ Pure p2 ⌈ Ok (VInt z2), emp ⌉ →
  Γ ⊢ ⌈ emp ⌉ Pure (PEq p1 p2) ⌈ Ok (VBool (Z.eqb z1 z2)), emp ⌉
| R_Assume : ∀ Γ,
  Γ ⊢ ⌈ emp ⌉ Assume TTrue ⌈ Ok VUnit, emp ⌉
| R_Error : ∀ Γ,
  Γ ⊢ ⌈ emp ⌉ Error ⌈ Err ECrash, emp ⌉
| R_Let : ∀ Γ x e1 e2 P Q R v ε,
  Γ ⊢ ⌈ P ⌉ e1 ⌈ Ok v, R ⌉ → Γ ⊢ ⌈ R ⌉ subst x v e2 ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Let x e1 e2 ⌈ ε, Q ⌉
| R_LetCut : ∀ Γ x e1 e2 P Q ξ,
  Γ ⊢ ⌈ P ⌉ e1 ⌈ Err ξ, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Let x e1 e2 ⌈ Err ξ, Q ⌉
| R_Choice1 : ∀ Γ e1 e2 P Q ε,
  Γ ⊢ ⌈ P ⌉ e1 ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Choice e1 e2 ⌈ ε, Q ⌉
| R_Choice2 : ∀ Γ e1 e2 P Q ε,
  Γ ⊢ ⌈ P ⌉ e2 ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Choice e1 e2 ⌈ ε, Q ⌉
| R_Loop : ∀ Γ e P Q ε,
  Γ ⊢ ⌈ P ⌉ Let BAnon e (Loop e) ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ P ⌉ Loop e ⌈ ε, Q ⌉
| R_LoopCut : ∀ Γ e P,
  Γ ⊢ ⌈ P ⌉ Loop e ⌈ Ok VUnit, P ⌉
| R_Alloc : ∀ Γ l,
  Γ ⊢ ⌈ emp ⌉ Alloc ⌈ Ok (VLoc l), PLoc l ↦? ⌉
| R_Free : ∀ Γ t v,
  Γ ⊢ ⌈ Term t ↦ PVal v ⌉ Free t ⌈ Ok VUnit, Term t ↦∅ ⌉
| R_FreeUninit : ∀ Γ t,
  Γ ⊢ ⌈ Term t ↦? ⌉ Free t ⌈ Ok VUnit, Term t ↦∅ ⌉
| R_FreeFreed : ∀ Γ t,
  Γ ⊢ ⌈ Term t ↦∅ ⌉ Free t ⌈ Err ECrash, Term t ↦∅ ⌉
| R_Store : ∀ Γ t1 t2 v,
  Γ ⊢ ⌈ Term t1 ↦ PVal v ⌉ Store t1 t2 ⌈ Ok VUnit, Term t1 ↦ Term t2 ⌉
| R_StoreUninit : ∀ Γ t1 t2,
  Γ ⊢ ⌈ Term t1 ↦? ⌉ Store t1 t2 ⌈ Ok VUnit, Term t1 ↦ Term t2 ⌉
| R_StoreFreed : ∀ Γ t1 t2,
  Γ ⊢ ⌈ Term t1 ↦∅ ⌉ Store t1 t2 ⌈ Err ECrash, Term t1 ↦∅ ⌉
| R_Load : ∀ Γ t v,
  Γ ⊢ ⌈ Term t ↦ PVal v ⌉ Load t ⌈ Ok v, Term t ↦ PVal v ⌉
| R_LoadUninit : ∀ Γ t,
  Γ ⊢ ⌈ Term t ↦? ⌉ Load t ⌈ Err ECrash, Term t ↦? ⌉
| R_LoadFreed : ∀ Γ t,
  Γ ⊢ ⌈ Term t ↦∅ ⌉ Load t ⌈ Err ECrash, Term t ↦∅ ⌉
| R_Frame : ∀  Γ e P Q R ε,
  Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ P ∗ R ⌉ e ⌈ ε, Q ∗ R ⌉
| R_Disj : ∀ Γ e P1 P2 Q1 Q2 ε,
  Γ ⊢ ⌈ P1 ⌉ e ⌈ ε, Q1 ⌉ → Γ ⊢ ⌈ P2 ⌉ e ⌈ ε, Q2 ⌉ →
  Γ ⊢ ⌈ P1 ∨∨ P2 ⌉ e ⌈ ε, Q1 ∨∨ Q2 ⌉
| R_Cons : ∀ Γ Γ' e P P' Q Q' ε,
  Γ' ⊆ Γ → (⊢ (P' ⇒ P)) → (⊢ (Q ⇒ Q')) → Γ' ⊢ ⌈ P' ⌉ e ⌈ ε , Q' ⌉ →
  Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉
| R_Exist : ∀ Γ e P Q ε X,
  Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ⌉ →
  Γ ⊢ ⌈ ∃∃ x ⋮ X, P ⌉ e ⌈ ε, ∃∃ x ⋮ X, Q ⌉
| R_Call : ∀ Γ f ts vs P Q ε specs,
  Γ !! f = Some specs → [(vs) P | ε, Q] ∈ specs → ts = Vals vs →
  Γ ⊢ ⌈ P ⌉ Call f ts ⌈ ε , Q ⌉
where "Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉" := (ux_rule Γ P e ε Q).

(* Environment validity *)
Reserved Notation "γ ≺ₛ Γ"
  (at level 100, no associativity).
Inductive ux_env_rule : impl_ctx → spec_ctx → Prop :=
| R_Empty :
  ∅ ≺ₛ ∅
| R_Imp : ∀ γ γ' Γ Γ' f xs e,
  (γ ≺ₛ Γ) →
  f ∉ dom γ → γ' = <[f := {(xs) e}]>γ →
  Γ' = <[f := []]>Γ →
  γ' ≺ₛ Γ'
| R_Spec : ∀ γ Γ Γ' P Q ε f i e vs,
  (γ ≺ₛ Γ) → Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉ →
  γ !! f = Some i → subst_vals (params i) vs (body i) = Some e →
  Γ' = alter (cons [(vs) P | ε, Q]) f Γ →
  γ ≺ₛ Γ'
where "γ ≺ₛ Γ" := (ux_env_rule γ Γ).


(*** Soundness ***)

(* UX rule definition *)
Definition ux_triple (γ : impl_ctx) (e : expr) (P Q : hprop) (ε : exit) : Prop :=
  ∀ h', Q h' → ∃ h, P h ∧ (γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩) ∧ ((∃ v, ε = Ok v) ∨ (∃ ξ, ε = Err ξ)).
Definition valid_specs (γ : impl_ctx) (Γ : spec_ctx) : Prop :=
  ∀ f S, Γ !! f = Some S → ∀ s, s ∈ S → ∃ i e, γ !! f = Some i ∧
  subst_vals (params i) (vals s) (body i) = Some e ∧
  ux_triple γ e (pre s) (post s) (tag s).
Definition ux_spec (Γ : spec_ctx) (e : expr) (P Q : hprop) (ε : exit) : Prop :=
  ∀ γ, valid_specs γ Γ → ux_triple γ e P Q ε.

(* Properties *)
Lemma env_inclusion (γ : impl_ctx) (Γ Γ' : spec_ctx) :
  valid_specs γ Γ → Γ' ⊆ Γ → valid_specs γ Γ'.
Proof.
  intros Hval Hsub f S Hsome' s Hin. rewrite (map_subseteq_spec Γ') in Hsub.
  specialize (Hsub _ _ Hsome') as Hsome. by specialize (Hval _ _ Hsome _ Hin).
Qed.

(* Soundness of proof rules *)
Theorem ux_soundness Γ P e ε Q :
  Γ ⊢ ⌈ P ⌉ e ⌈ ε , Q ⌉ → ux_spec Γ e P Q ε.
Proof.
  intros rule; induction rule.
  + intros γ Hval h Hemp.
    exists h. split; first done. split; last by left; exists v.
    by apply O_Pure.
  + intros γ Hval h' HQ.
    specialize (IHrule _ Hval _ HQ) as [h [HP [Hstep Hε]]].
    inversion HQ; inversion Hstep; subst.
    exists ∅. split; first done. split; last by left; exists (VInt (-z)).
    by apply O_Pure, pure_neg_Ok.
  + intros γ Hval h' HQ.
    specialize (IHrule _ Hval _ HQ) as [h [HP [Hstep Hε]]].
    inversion HQ; inversion Hstep; subst.
    exists ∅. split; first done. split; last by left; exists (VBool (negb b)).
    by apply O_Pure, pure_not_Ok.
  + intros γ Hval h' HQ.
    specialize (IHrule1 _ Hval _ HQ) as [h1 [HP1 [Hstep1 Hε1]]].
    specialize (IHrule2 _ Hval _ HQ) as [h2 [HP2 [Hstep2 Hε2]]].
    inversion HQ; inversion Hstep1; inversion Hstep2; subst.
    exists ∅. split; first done. split; last by left; exists (VInt (z1 + z2)).
    by apply O_Pure, pure_plus_Ok.
  + intros γ Hval h' HQ.
    specialize (IHrule1 _ Hval _ HQ) as [h1 [HP1 [Hstep1 Hε1]]].
    specialize (IHrule2 _ Hval _ HQ) as [h2 [HP2 [Hstep2 Hε2]]].
    inversion HQ; inversion Hstep1; inversion Hstep2; subst.
    exists ∅. split; first done. split; last by left; exists (VBool (Z.eqb z1 z2)).
    by apply O_Pure, pure_eq_Ok.
  + intros γ Hval h Hemp.
    exists h. split; first done. split; last by left; exists VUnit.
    by apply O_Assume.
  + intros γ Hval h Hemp.
    exists h. split; first done. split; last by right; exists ECrash.
    by apply O_Error.
  + intros γ Hval h' HQ.
    specialize (IHrule2 _ Hval _ HQ) as [h'' [HR [Hstep Hε]]].
    specialize (IHrule1 _ Hval _ HR) as [h [HP [Hstep' Hε']]].
    exists h. split; first done. split; last done.
    by eapply O_Let.
  + intros γ Hval h' HQ.
    specialize (IHrule _ Hval _ HQ) as [h [HP [Hstep Hε]]].
    exists h. split; first done. split; last done.
    by eapply O_LetErr.
  + intros γ Hval h' HQ.
    specialize (IHrule _ Hval _ HQ) as [h [HP [Hstep Hε]]].
    exists h. split; first done. split; last done.
    by eapply O_Choice1.
  + intros γ Hval h' HQ.
    specialize (IHrule _ Hval _ HQ) as [h [HP [Hstep Hε]]].
    exists h. split; first done. split; last done.
    by eapply O_Choice2.
  + intros γ Hval h' HQ.
    specialize (IHrule _ Hval _ HQ) as [h [HP [Hstep Hε]]].
    exists h. split; first done. split; last done.
    by eapply O_Loop.
  + intros γ Hval h HP.
    exists h. split; first done. split; last by left; exists VUnit.
    by apply O_LoopCut.
  + intros γ Hval h [l' [Hpure Hheap]].
    inversion Hpure; subst.
    exists ∅. split; first done. split; last by left; exists (VLoc l').
    by apply O_Alloc.
  + intros γ Hval h [l [Hpure Hheap]].
    destruct t; inversion Hpure; subst.
    set (h := (<[l := Freed]>{[l := LangVal v]} : heap)).
    replace {[l := Freed]} with h by eapply insert_singleton.
    exists {[l := LangVal v]}. split; first by exists l, v. split; last by left; exists VUnit.
    by eapply O_Free; try apply lookup_insert.
  + intros γ Hval h [l [Hpure Hheap]].
    destruct t; inversion Hpure; subst.
    set (h := (<[l := Freed]>{[l := Poison]} : heap)).
    replace {[l := Freed]} with h by eapply insert_singleton.
    exists {[l := Poison]}. split; first by exists l. split; last by left; exists VUnit.
    by eapply O_Free; try apply lookup_insert.
  + intros γ Hval h [l [Hpure Hheap]].
    destruct t; inversion Hpure; subst.
    exists {[l := Freed]}. split; first by exists l. split; last by right; exists ECrash.
    by eapply O_FreeErr; try apply lookup_insert.
  + intros γ Hval h [l [v2 [Hpure1 [Hpure2 Hheap]]]].
    destruct t1; inversion Hpure1; subst.
    destruct t2; inversion Hpure2; subst.
    set (h := <[l := LangVal v2]>{[l := LangVal v]} : heap).
    replace {[l := LangVal v2]} with h by eapply insert_singleton.
    exists {[l := LangVal v]}. split; first by exists l, v. split; last by left; exists VUnit.
    by eapply O_Store; try apply lookup_insert.
  + intros γ Hval h [l [v2 [Hpure1 [Hpure2 Hheap]]]].
    destruct t1; inversion Hpure1; subst.
    destruct t2; inversion Hpure2; subst.
    set (h := (<[l := LangVal v2]>{[l := Poison]} : heap)).
    replace {[l := LangVal v2]} with h by eapply insert_singleton.
    exists {[l := Poison]}. split; first by exists l. split; last by left; exists VUnit.
    by eapply O_Store; try apply lookup_insert.
  + intros γ Hval h [l [Hpure1 Hheap]].
    destruct t1; inversion Hpure1; subst.
    exists {[l := Freed]}. split; first by exists l. split; last by right; exists ECrash.
    by eapply O_StoreErr; try apply lookup_insert.
  + intros γ Hval h [l [vl [Hpurel [Hpurev Hheap]]]].
    destruct t; inversion Hpurel; subst.
    inversion Hpurev; subst.
    exists {[l := LangVal vl]}. split; first by exists l, vl. split; last by left; exists vl.
    by eapply O_Load; try apply lookup_insert.
  + intros γ Hval h [l [Hpure Hheap]].
    destruct t; inversion Hpure; subst.
    exists {[l := Poison]}. split; first by exists l. split; last by right; exists ECrash.
    by eapply O_LoadErr; try right; try apply lookup_insert.
  + intros γ Hval h [l [Hpure Hheap]].
    destruct t; inversion Hpure; subst.
    exists {[l := Freed]}. split; first by exists l. split; last by right; exists ECrash.
    by eapply O_LoadErr; try left; try apply lookup_insert.
  + intros γ Hval h' [hQ [hR [-> [Hdisj [HQ HR]]]]].
    specialize (IHrule _ Hval _ HQ) as [hP [HP [Hstep Hε]]].
    specialize (ux_frame _ _ _ _ _ Hstep Hε _ _ Hdisj (map_disjoint_empty_r γ)).
    rewrite (map_union_empty γ). intros [].
    exists (hP ∪ hR). split; last done. by exists hP, hR.
  + intros γ Hval h' [HQ1|HQ2].
    - specialize (IHrule1 _ Hval _ HQ1) as [h [HP [Hstep Hε]]].
      exists h. split; last done. by left.
    - specialize (IHrule2 _ Hval _ HQ2) as [h [HP [Hstep Hε]]].
      exists h. split; last done. by right.
  + intros γ Hval h' HQ.
    assert (⊢ (Q ⇒ Q')) as HQent by done; apply HQent in HQ.
    eapply env_inclusion in Hval; last done.
    specialize (IHrule _ Hval _ HQ) as [h [HP [Hstep Hε]]].
    assert (⊢ (P' ⇒ P)) as HPent by done; apply HPent in HP.
    by exists h.
  + intros γ Hval h' [v HQ].
    specialize (IHrule _ Hval _ HQ) as [h [HP [Hstep Hε]]].
    exists h. by split; first by exists v.
  + intros γ Hval h' HQ. subst.
    assert (Γ !! f = Some specs ∧ [ (vs) P | ε, Q] ∈ specs) as [HΓsome Hspec] by done.
    specialize (Hval _ _ HΓsome _ Hspec) as [i [e [Hγsome [Hsubst Hux]]]].
    specialize (Hux _ HQ) as [h [HP [Hstep Hε]]].
    exists h. split; first done. split; last done.
    by eapply O_Call.
Qed.

(* Soundness of environment validity *)
Theorem env_soundness γ Γ :
  (γ ≺ₛ Γ) → valid_specs γ Γ.
Proof.
  intros rule; induction rule; subst.
  + done.
  + intros f' S HΓsome s Hin.
    apply lookup_insert_Some in HΓsome as [[_ <-]|[? HΓsome]]; first inversion Hin.
    specialize (IHrule _ _ HΓsome _ Hin) as [i [es [Hγsome [Hsubst Hux]]]].
    exists i, es. split; first by rewrite (lookup_insert_ne γ). split; first done.
    intros h' HQ. specialize (Hux _ HQ) as [h [HP [Hstep Hε]]].
    exists h. split; first done. split; last done.
    rewrite (insert_union_singleton_r γ); last by apply not_elem_of_dom.
    rewrite <- (map_union_empty h), <- (map_union_empty h').
    apply ux_frame; try done; first apply map_disjoint_empty_r.
    by apply map_disjoint_singleton_r, not_elem_of_dom.
  + intros f' specs HΓsome s Hin.
    apply lookup_alter_Some in HΓsome as [[<- [? [? ->]]]|[]]; last by eapply IHrule.
    assert (Γ ⊢ ⌈ P ⌉ e ⌈ ε, Q ⌉) as Hrule by done.
    specialize (ux_soundness _ _ _ _ _ Hrule _ IHrule); intros Hux.
    apply elem_of_cons in Hin as [->|]; last by eapply IHrule. by exists i, e.
Qed.
