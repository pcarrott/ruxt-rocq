From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.


(*** Program context ***)

(* Function implementations *)
Record fun_impl := mk_fun_impl { params : list string; body : expr }.
Notation "{ ( xs ) e }" := (mk_fun_impl xs e).
Definition impl_ctx := gmap string fun_impl.
(* Heaps *)
Inductive heap_value := HVal (v : val) | Poison.
Definition block_heap := gmap nat heap_value.
Inductive block_value := BVal (sz : nat) (bh : block_heap) | Freed.
Definition heap := gmap block block_value.
(* Heap operations *)
Fixpoint breplicate (hv : heap_value) (n : nat) : block_heap :=
  match n with O => ∅ | S n => <[ n := hv ]> (breplicate hv n) end.
Notation balloc := (breplicate Poison).
Definition bupdate (bh : block_heap) (i : nat) (v : val) : block_heap :=
  <[ i := HVal v ]> bh.
Definition hupdate (h : heap) (b : block) (bv : block_value) : heap :=
  <[ b := bv ]>h.
Notation hstore h b sz bh := (hupdate h b (BVal sz bh)).
Notation hfree h b := (hupdate h b Freed).
(* Properties *)
Lemma hupdate_disj h h' b bv :
  hupdate h b bv ##ₘ h' ↔ h ##ₘ h' ∧ b ∉ dom h'.
Proof.
  unfold hupdate; split.
  + by intros [?%not_elem_of_dom Hdisj]%map_disjoint_insert_l.
  + intros [Hdisj Hnin]. apply map_disjoint_insert_l.
    by split; first apply not_elem_of_dom.
Qed.
Lemma hupdate_union h h' b bv :
  hupdate h b bv ##ₘ h' → hupdate h b bv ∪ h' = hupdate (h ∪ h') b bv.
Proof.
  intros Hdisj. symmetry; apply insert_union_l.
Qed.


(*** Termination ***)

(* Termination tags *)
Inductive exit := Ok (v : val) | Err | Miss (l : loc).
Global Instance exit_eq_dec : EqDecision exit.
Proof. solve_decision. Defined.
Global Instance exit_countable : Countable exit.
Proof.
  refine (inj_countable' (λ ε, match ε with
  | Ok v => (inl (Some v)) | Err => (inl None) | Miss l => (inr l)
  end) (λ s, match s with
  | (inl (Some v)) => Ok v | (inl None) => Err | (inr l) => Miss l
  end) _); by intros [].
Qed.


(*** Operational semantics ***)

(* Full semantics *)
Reserved Notation "γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩".
Inductive eval_expr : impl_ctx → heap → expr → heap → exit → Prop :=
| O_Pure γ p h v :
  ⌊ p ⌋ₚ = Some v →
  γ ⊢ ⟨ h | Pure p ⟩ ⇓ ⟨ h | Ok v ⟩
| O_Assume γ h :
  γ ⊢ ⟨ h | Assume TTrue ⟩ ⇓ ⟨ h | Ok VUnit ⟩
| O_Error γ h :
  γ ⊢ ⟨ h | Error ⟩ ⇓ ⟨ h | Err ⟩
| O_Let γ x e1 e2 h h' h'' v ε :
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h'' | Ok v ⟩ → γ ⊢ ⟨ h'' | e2⌊v//x⌋ ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_LetErr γ x e1 e2 h h' :
  γ ⊢ ⟨ h | e1 ⟩ ⇓ ⟨ h' | Err ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ ⟨ h' | Err ⟩
| O_Choice γ ei e1 e2 h h' ε :
  γ ⊢ ⟨ h | ei ⟩ ⇓ ⟨ h' | ε ⟩ → (ei = e1 ∨ ei = e2) →
  γ ⊢ ⟨ h | Choice e1 e2 ⟩ ⇓ ⟨ h' | ε ⟩
| O_Alloc γ t h h' l n :
  ⌊ t ⌋ₜ = Some (VInt (Z.of_nat n)) →
  l.1 ∉ dom h → l.2 = 0 →
  h' = hstore h l.1 n (balloc n) →
  γ ⊢ ⟨ h | Alloc t ⟩ ⇓ ⟨ h' | Ok (VLoc l) ⟩
| O_Free γ t h h' l sz bh :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → l.2 = 0 → (∀ i, i < sz → i ∈ dom bh) →
  h' = hfree h l.1 →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h' | Ok VUnit ⟩
| O_FreeErr γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  l.2 ≠ 0 →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Err ⟩
| O_FreeErrBlock γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some Freed →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Err ⟩
| O_FreeMiss γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  l.1 ∉ dom h →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Err ⟩
| O_FreeMissBlock γ t h l sz bh i :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → i < sz → i ∉ dom bh →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ ⟨ h | Err ⟩
| O_Store γ t1 t2 h h' l sz bh v :
  ⌊ t1 ⌋ₜ = Some (VLoc l) → ⌊ t2 ⌋ₜ = Some v →
  h !! l.1 = Some (BVal sz bh) → l.2 ∈ dom bh →
  h' = hstore h l.1 sz (bupdate bh l.2 v) →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h' | Ok VUnit⟩
| O_StoreErr γ t1 t2 h l :
  ⌊ t1 ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some Freed →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h | Err ⟩
| O_StoreMiss γ t1 t2 h l :
  ⌊ t1 ⌋ₜ = Some (VLoc l) →
  l.1 ∉ dom h →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h | Err ⟩
| O_StoreMissBlock γ t1 t2 h l sz bh :
  ⌊ t1 ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → l.2 ∉ dom bh →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ ⟨ h | Err ⟩
| O_Load γ t h l sz bh v :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → bh !! l.2 = Some (HVal v) →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Ok v ⟩
| O_LoadErr γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some Freed →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Err ⟩
| O_LoadErrBlock γ t h l sz bh :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → bh !! l.2 = Some Poison →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Err ⟩
| O_LoadMiss γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  l.1 ∉ dom h →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Err ⟩
| O_LoadMissBlock γ t h l sz bh :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → l.2 ∉ dom bh →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ ⟨ h | Err ⟩
| O_Call γ f xs e ts h h' ε :
  γ !! f = Some {(xs) e} → γ ⊢ ⟨ h | e⌊ts[//]xs⌋ₜ ⟩ ⇓ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Call f ts ⟩ ⇓ ⟨ h' | ε ⟩
where "γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩" := (eval_expr γ h e h' ε).

(* Instrumental semantics *)
Reserved Notation "γ ⊢ ⟨ h | e ⟩ ⇓ᵢ ⟨ h' | ε ⟩".
Inductive eval_expr_frame : impl_ctx → heap → expr → heap → exit → Prop :=
| F_Pure γ p h v :
  ⌊ p ⌋ₚ = Some v →
  γ ⊢ ⟨ h | Pure p ⟩ ⇓ᵢ ⟨ h | Ok v ⟩
| F_Assume γ h :
  γ ⊢ ⟨ h | Assume TTrue ⟩ ⇓ᵢ ⟨ h | Ok VUnit ⟩
| F_Error γ h :
  γ ⊢ ⟨ h | Error ⟩ ⇓ᵢ ⟨ h | Err ⟩
| F_Let γ x e1 e2 h h' h'' v ε :
  γ ⊢ ⟨ h | e1 ⟩ ⇓ᵢ ⟨ h'' | Ok v ⟩ → γ ⊢ ⟨ h'' | e2⌊v//x⌋ ⟩ ⇓ᵢ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ᵢ ⟨ h' | ε ⟩
| F_LetErr γ x e1 e2 h h' :
  γ ⊢ ⟨ h | e1 ⟩ ⇓ᵢ ⟨ h' | Err ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ᵢ ⟨ h' | Err ⟩
| F_LetMiss γ x e1 e2 h h' m :
  γ ⊢ ⟨ h | e1 ⟩ ⇓ᵢ ⟨ h' | Miss m ⟩ →
  γ ⊢ ⟨ h | Let x e1 e2 ⟩ ⇓ᵢ ⟨ h' | Miss m ⟩
| F_Choice γ ei e1 e2 h h' ε :
  γ ⊢ ⟨ h | ei ⟩ ⇓ᵢ ⟨ h' | ε ⟩ → (ei = e1 ∨ ei = e2) →
  γ ⊢ ⟨ h | Choice e1 e2 ⟩ ⇓ᵢ ⟨ h' | ε ⟩
| F_Alloc γ t h h' l n :
  ⌊ t ⌋ₜ = Some (VInt (Z.of_nat n)) →
  l.1 ∉ dom h → l.2 = 0 →
  h' = hstore h l.1 n (balloc n) →
  γ ⊢ ⟨ h | Alloc t ⟩ ⇓ᵢ ⟨ h' | Ok (VLoc l) ⟩
| F_Free γ t h h' l sz bh :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → l.2 = 0 → (∀ i, i < sz → i ∈ dom bh) →
  h' = hfree h l.1 →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ᵢ ⟨ h' | Ok VUnit ⟩
| F_FreeErr γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  l.2 ≠ 0 →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ᵢ ⟨ h | Err ⟩
| F_FreeErrBlock γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some Freed →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ᵢ ⟨ h | Err ⟩
| F_FreeMiss γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  l.1 ∉ dom h →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ᵢ ⟨ h | Miss l ⟩
| F_FreeMissBlock γ t h l sz bh i :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → i < sz → i ∉ dom bh →
  γ ⊢ ⟨ h | Free t ⟩ ⇓ᵢ ⟨ h | Miss (l +ₗ i) ⟩
| F_Store γ t1 t2 h h' l sz bh v :
  ⌊ t1 ⌋ₜ = Some (VLoc l) → ⌊ t2 ⌋ₜ = Some v →
  h !! l.1 = Some (BVal sz bh) → l.2 ∈ dom bh →
  h' = hstore h l.1 sz (bupdate bh l.2 v) →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ᵢ ⟨ h' | Ok VUnit⟩
| F_StoreErr γ t1 t2 h l :
  ⌊ t1 ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some Freed →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ᵢ ⟨ h | Err ⟩
| F_StoreMiss γ t1 t2 h l :
  ⌊ t1 ⌋ₜ = Some (VLoc l) →
  l.1 ∉ dom h →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ᵢ ⟨ h | Miss l ⟩
| F_StoreMissBlock γ t1 t2 h l sz bh :
  ⌊ t1 ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → l.2 ∉ dom bh →
  γ ⊢ ⟨ h | Store t1 t2 ⟩ ⇓ᵢ ⟨ h | Miss l ⟩
| F_Load γ t h l sz bh v :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → bh !! l.2 = Some (HVal v) →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ᵢ ⟨ h | Ok v ⟩
| F_LoadErr γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some Freed →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ᵢ ⟨ h | Err ⟩
| F_LoadErrBlock γ t h l sz bh :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → bh !! l.2 = Some Poison →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ᵢ ⟨ h | Err ⟩
| F_LoadMiss γ t h l :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  l.1 ∉ dom h →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ᵢ ⟨ h | Miss l ⟩
| F_LoadMissBlock γ t h l sz bh :
  ⌊ t ⌋ₜ = Some (VLoc l) →
  h !! l.1 = Some (BVal sz bh) → l.2 ∉ dom bh →
  γ ⊢ ⟨ h | Load t ⟩ ⇓ᵢ ⟨ h | Miss l ⟩
| F_Call γ f xs e ts h h' ε :
  γ !! f = Some {(xs) e} → γ ⊢ ⟨ h | e⌊ts[//]xs⌋ₜ ⟩ ⇓ᵢ ⟨ h' | ε ⟩ →
  γ ⊢ ⟨ h | Call f ts ⟩ ⇓ᵢ ⟨ h' | ε ⟩
where "γ ⊢ ⟨ h | e ⟩ ⇓ᵢ ⟨ h' | ε ⟩" := (eval_expr_frame γ h e h' ε).

(* Under-approximate frame validity - frame addition *)
Theorem frame_addition γ h e h' ε :
  γ ⊢ ⟨ h | e ⟩ ⇓ᵢ ⟨ h' | ε ⟩ →
  ∀ hF, h' ##ₘ hF →
  (γ ⊢ ⟨ h ∪ hF | e ⟩ ⇓ᵢ ⟨ h' ∪ hF | ε ⟩ ∧ h ##ₘ hF) ∨
  (∃ l, ε = Miss l ∧ l.1 ∈ dom hF).
Proof.
  intros Hstep.
  induction Hstep; intros hF Hframe'.
  + left. by split; first apply F_Pure.
  + left. by split; first apply F_Assume.
  + left. by split; first apply F_Error.
  + specialize (IHHstep2 _ Hframe') as [[Hstep2F Hframe'']|]; last by right.
    specialize (IHHstep1 _ Hframe'') as [[Hstep1F Hframe]|[?[]]]; last by exfalso.
    left. by split; first eapply F_Let.
  + specialize (IHHstep _ Hframe') as [[HstepF Hframe]|]; last by right.
    left. by split; first apply F_LetErr.
  + specialize (IHHstep _ Hframe') as [[HstepF Hframe]|]; last by right.
    left. by split; first apply F_LetMiss.
  + specialize (IHHstep _ Hframe') as [[HstepF Hframe]|]; last by right.
    left. by split; first eapply F_Choice.
  + left. subst. rewrite hupdate_union; last done.
    apply hupdate_disj in Hframe' as [? Hnin].
    split; first eapply F_Alloc; try done. set_solver.
  + left. subst. rewrite hupdate_union; last done.
    apply hupdate_disj in Hframe' as [].
    split; first eapply F_Free; try done.
    apply lookup_union_Some_raw; by left.
  + left. split; last done. by eapply F_FreeErr.
  + left. split; last done. eapply F_FreeErrBlock; try done.
    apply lookup_union_Some_raw; by left.
  + destruct (hF !! l.1) as [hv|] eqn:Hlookup.
    - right. eexists. split; first done.
      apply elem_of_dom. by eexists.
    - left. split; last done. eapply F_FreeMiss; try done.
      assert (l.1 ∉ dom h) as Hnin by assumption.
      intros Hin%dom_union. apply Hnin.
      apply elem_of_union in Hin as []; first done.
      rewrite <- not_elem_of_dom in Hlookup. by exfalso.
  + left. split; last done. eapply F_FreeMissBlock; try done.
    apply lookup_union_Some_raw; by left.
  + subst. unfold hupdate in *.
    apply map_disjoint_insert_l in Hframe' as [_ Hframe].
    rewrite <- (insert_union_l h).
    left. split; last done. eapply F_Store; try done.
    apply lookup_union_Some_raw; by left.
  + left. split; last done. eapply F_StoreErr; try done.
    apply lookup_union_Some_raw; by left.
  + destruct (hF !! l.1) as [hv|] eqn:Hlookup.
    - right. eexists. split; first done.
      apply elem_of_dom. by eexists.
    - left. split; last done. eapply F_StoreMiss; try done.
      intros Hin%dom_union.
      apply elem_of_union in Hin as []; first done.
      rewrite <- not_elem_of_dom in Hlookup. by exfalso.
  + left. split; last done. eapply F_StoreMissBlock; try done.
    apply lookup_union_Some_raw; by left.
  + left. split; last done. eapply F_Load; try done.
    apply lookup_union_Some_raw; by left.
  + left. split; last done. eapply F_LoadErr; try done.
    apply lookup_union_Some_raw; by left.
  + left. split; last done. eapply F_LoadErrBlock; try done.
    apply lookup_union_Some_raw; by left.
  + destruct (hF !! l.1) as [hv|] eqn:Hlookup.
    - right. eexists. split; first done.
      apply elem_of_dom. by eexists.
    - left. split; last done. eapply F_LoadMiss; try done.
      assert (l.1 ∉ dom h) as Hnin by assumption.
      intros Hin%dom_union. apply Hnin.
      apply elem_of_union in Hin as []; first done.
      rewrite <- not_elem_of_dom in Hlookup. by exfalso.
  + left. split; last done. eapply F_LoadMissBlock; try done.
    apply lookup_union_Some_raw; by left.
  + specialize (IHHstep _ Hframe') as [[HstepF Hframe]|]; last by right.
    left. split; last done. eapply F_Call; try done.
Qed.

(* Over-approximate frame validity - frame subtraction *)
Theorem frame_subtraction γ h e h' ε :
  γ ⊢ ⟨ h | e ⟩ ⇓ᵢ ⟨ h' | ε ⟩ →
  ∀ hs hF, h = hs ∪ hF → hs ##ₘ hF →
  ∃ hs', hs' ##ₘ hF ∧ (
    (γ ⊢ ⟨ hs | e ⟩ ⇓ᵢ ⟨ hs' | ε ⟩ ∧ h' = hs' ∪ hF) ∨
    (∃ l, γ ⊢ ⟨ hs | e ⟩ ⇓ᵢ ⟨ hs' | Miss l ⟩ ∧ l.1 ∈ dom hF)
  ).
Proof.
  intros Hstep.
  induction Hstep; intros hs hF Hheap Hframe.
  + eexists. split; first done.
    left. by split; first apply F_Pure.
  + eexists. split; first done.
    left. by split; first apply F_Assume.
  + eexists. split; first done.
    left. by split; first apply F_Error.
  + specialize (IHHstep1 _ _ Hheap Hframe) as [hs'' [Hframe'' Hstep1F]].
    destruct Hstep1F as [[Hstep1F Hheap'']|[ms [Hmiss Hdom]]].
    - specialize (IHHstep2 _ _ Hheap'' Hframe'') as [hs' [Hframe' Hstep2F]].
      eexists. split; first done.
      destruct Hstep2F as [[Hstep2F Hheap']|[ms [Hmiss Hdom]]].
      * left. by split; first eapply F_Let.
      * right. eexists. by split; first eapply F_Let.
    - eexists. split; first done.
      right. eexists. by split; first apply F_LetMiss.
  + specialize (IHHstep _ _ Hheap Hframe) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[ms [Hmiss Hdom]]].
    - left. by split; first apply F_LetErr.
    - right. eexists. by split; first apply F_LetMiss.
  + specialize (IHHstep _ _ Hheap Hframe) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[ms [Hmiss Hdom]]].
    - left. by split; first apply F_LetMiss.
    - right. eexists. by split; first apply F_LetMiss.
  + specialize (IHHstep _ _ Hheap Hframe) as [hs' [Hframe' HstepF]].
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. by split; first eapply F_Choice.
    - right. eexists. by split; first eapply F_Choice.
  + assert (hstore hs l.1 n (balloc n) ##ₘ hF) as Hdisj.
    { apply hupdate_disj. set_solver. }
    eexists. split; first done. left.
    split; last by (subst; rewrite hupdate_union).
    by eapply F_Alloc; try done; last set_solver.
  + subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - assert (hF !! l.1 = None) by by eapply map_disjoint_Some_l in Hframe.
      eexists. split. eapply hupdate_disj;
        first by split; last apply not_elem_of_dom.
      left. split; first by eapply F_Free.
      symmetry; apply hupdate_union, hupdate_disj;
        first by split; last apply not_elem_of_dom.
    - eexists. split; first done.
      right. eexists. split; first by eapply F_FreeMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. by eapply F_FreeErr.
  + eexists. split; first done.
    subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply F_FreeErrBlock.
    - right. eexists. split; first by eapply F_FreeMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. eapply F_FreeMiss; try done. set_solver.
  + eexists. split; first done.
    subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply F_FreeMissBlock.
    - right. eexists. split; first by eapply F_FreeMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - eexists. split; first by eapply map_disjoint_Some_insert.
      left. split; last by rewrite <- insert_union_l. by eapply F_Store.
    - eexists. split; first done.
      right. eexists. split; first by apply F_StoreMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply F_StoreErr.
    - right. eexists. split; first by apply F_StoreMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply F_StoreMiss; first done. set_solver.
  + eexists. split; first done.
    subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply F_StoreMissBlock.
    - right. eexists. split; first by eapply F_StoreMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply F_Load.
    - right. eexists. split; first by apply F_LoadMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply F_LoadErr.
    - right. eexists. split; first by apply F_LoadMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply F_LoadErrBlock.
    - right. eexists. split; first by eapply F_LoadMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + eexists. split; first done.
    left. split; last done. apply F_LoadMiss; first done. set_solver.
  + eexists. split; first done.
    subst; assert (_ !! l.1 = Some _) as Hlookup by done.
    apply lookup_union_Some_raw in Hlookup as [HSome|[HNone _]].
    - left. by split; first eapply F_LoadMissBlock.
    - right. eexists. split; first by eapply F_LoadMiss, not_elem_of_dom.
      by eapply map_union_dom; first eexists.
  + specialize (IHHstep _ _ Hheap Hframe) as [hs' [Hframe' HstepF]].
    subst; assert (_ !! f = Some _) as Hlookup by done.
    eexists. split; first done.
    destruct HstepF as [[HstepF Hheap']|[m [Hmiss Hdom]]].
    - left. by split; first eapply F_Call.
    - right. eexists. by split; first eapply F_Call.
Qed.

(* Relating the instrumental semantics with the full semantics *)
Definition exit_in_full (ε : exit) : exit :=
  match ε with Miss _ => Err | ε => ε end.
Theorem semantics_preservation γ h e h' ε :
  γ ⊢ ⟨ h | e ⟩ ⇓ᵢ ⟨ h' | ε ⟩ → γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | exit_in_full ε ⟩.
Proof.
  intros Hstep. induction Hstep.
  + by apply O_Pure.
  + by apply O_Assume.
  + by apply O_Error.
  + by eapply O_Let.
  + by eapply O_LetErr.
  + by eapply O_LetErr.
  + by eapply O_Choice.
  + by eapply O_Alloc.
  + by eapply O_Free.
  + by eapply O_FreeErr.
  + by eapply O_FreeErrBlock.
  + by eapply O_FreeMiss.
  + by eapply O_FreeMissBlock.
  + by eapply O_Store.
  + by eapply O_StoreErr.
  + by eapply O_StoreMiss.
  + by eapply O_StoreMissBlock.
  + by eapply O_Load.
  + by eapply O_LoadErr.
  + by eapply O_LoadErrBlock.
  + by eapply O_LoadMiss.
  + by eapply O_LoadMissBlock.
  + by eapply O_Call.
Qed.
