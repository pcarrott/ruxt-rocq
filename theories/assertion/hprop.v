From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.
From RUXt.lang Require Import semantics.


(*** Assertion language ***)

(* Assertions *)
Inductive asrt :=
| APure (P : Prop)
| ATrue
| AFalse
| AAnd (a1 a2 : asrt)
| AOr (a1 a2 : asrt)
| AImplies (a1 a2 : asrt)
| AExists {X : Type} (P : X → asrt)
| AEmp
| ASingle (p1 p2 : pure)
| AUninit (p : pure)
| AFreed (p : pure)
| AStar (a1 a2 : asrt).
(* Classical logic *)
Notation "⌞ P ⌟" := (APure P).
Notation "'TRUE'" := ATrue.
Notation "'FALSE'" := AFalse.
Notation "P ∧ₕ Q" := (AAnd P Q) (at level 50).
Notation "P ∨ₕ Q" := (AOr P Q) (at level 50).
Notation "P →ₕ Q" := (AImplies P Q) (at level 50).
Notation "∃ₕ x , P" := (AExists (λ x, P)) (at level 50).
Notation "∃ₕ x ⋮ X , P" := (AExists (λ x : X, P)) (at level 50).
(* Separation logic *)
Notation "'EMP'" := AEmp.
Notation "p1 ↦ p2" := (ASingle p1 p2) (at level 50).
Notation "p '↦∅'" := (AFreed p) (at level 50).
Notation "p '↦?'" := (AUninit p) (at level 50).
Notation "H1 ∗ H2" := (AStar H1 H2) (at level 50).
(* Syntactic sugar *)
Definition AIter {X : Type} (xs : list X) (P : X → asrt) : asrt := 
  foldr AStar EMP (P <$> xs).
Notation "[∗ xs , P ]" := (AIter xs P) (at level 50).
Notation "⌜ P ⌝" := (P ∗ TRUE).

(* Assertion semantics *)
Fixpoint hprop (h : heap) (a : asrt) : Prop :=
  match a with
  | ⌞ P ⌟ => h = ∅ ∧ P
  | TRUE => True
  | FALSE => False
  | AAnd a1 a2 => hprop h a1 ∧ hprop h a2
  | AOr a1 a2 => hprop h a1 ∨ hprop h a2
  | AImplies a1 a2 => hprop h a1 → hprop h a2
  | AExists P => ∃ x, hprop h (P x)
  | AEmp => h = ∅
  | ASingle p1 p2 => ∃ l v, ⌊p1⌋ₚ = Some (VLoc l) ∧ ⌊p2⌋ₚ = Some v ∧ h = {[l := LangVal v]}
  | AUninit p => ∃ l, ⌊p⌋ₚ = Some (VLoc l) ∧ h = {[l := Poison]}
  | AFreed p => ∃ l, ⌊p⌋ₚ = Some (VLoc l) ∧ h = {[l := Freed]}
  | AStar a1 a2 => ∃ h1 h2, h = h1 ∪ h2 ∧ h1 ##ₘ h2 ∧ hprop h1 a1 ∧ hprop h2 a2
  end.
(* Entailment *)
Definition hentails (P Q : asrt) : Prop :=
  ∀ h, hprop h P → ∃ h', h' ⊆ h ∧ hprop h' Q.
Notation "H1 ⊨ H2" := (hentails H1 H2) (at level 50).
Definition hassert (P : asrt) : Prop :=
  ∀ h, hprop h P.
Notation "⊨ H" := (hassert H) (at level 50).


(*** Properties ***)

(* Heap assertions *)
Lemma hsingle_heap l v h :
  hprop h (PLoc l ↦ PVal v) ↔ h = {[l := LangVal v]}.
Proof.
  split; last by intros ->; do 2 eexists.
  intros [? [? [Hokl [Hokv ?]]]].
  by inversion Hokl; inversion Hokv; subst.
Qed.

(* Separating conjunction *)
Lemma hstar_comm P Q h :
  hprop h (P ∗ Q) ↔ hprop h (Q ∗ P).
Proof.
  split; intros [h'[?[->[?[]]]]];
    by rewrite (map_union_comm h'); first do 2 eexists.
Qed.
Lemma hstar_assoc P Q R h :
  hprop h ((P ∗ Q) ∗ R) ↔ hprop h (P ∗ (Q ∗ R)).
Proof.
  split.
  + intros [hstar[hR[->[Hdisj[[hP[hQ[->[HdisjPQ[HP HQ]]]]] HR]]]]].
    apply map_disjoint_union_l in Hdisj as [HdisjPR HdisjQR].
    rewrite <- (assoc_L (∪)). do 2 eexists. repeat split;
      first apply map_disjoint_union_r; try done.
    by do 2 eexists.
  + intros [hP[hQR[->[Hdisj[HP [hQ[hR[->[HdisjQR[HQ HR]]]]]]]]]].
    apply map_disjoint_union_r in Hdisj as [HdisjPQ HdisjPR].
    rewrite (assoc_L (∪)). do 2 eexists. repeat split;
      first apply map_disjoint_union_l; try done.
    by do 2 eexists.
Qed.

(* Iterated star *)
Lemma hiter_nil {X : Type} (P : X → asrt) h :
  hprop h ([∗ [] , P]) ↔ hprop h EMP.
Proof. done. Qed.
Lemma hiter_cons {X : Type} (P : X → asrt) x xs h :
  hprop h ([∗ x :: xs, P]) ↔ hprop h (P x ∗ [∗ xs, P]).
Proof. done. Qed.
Lemma hiter_singleton {X : Type} (P : X → asrt) x h :
  hprop h ([∗ [x], P]) ↔ hprop h (P x).
Proof.
  split.
  + intros [h'[?[->[?[HP Hemp]]]]]. inversion Hemp; subst.
    by rewrite <- (map_union_id_r h').
  + intros. rewrite hiter_cons.
    do 2 eexists. by repeat split;
      first apply map_union_id_r; first apply map_disjoint_empty_r.
Qed.
Lemma hiter_app {X : Type} (P : X → asrt) xs ys h :
  hprop h ([∗ xs ++ ys, P]) ↔ hprop h ([∗ xs, P] ∗ [∗ ys, P]).
Proof.
  split; revert h.
  + induction xs as [|a xs]; intros h Happ.
    - do 2 eexists. split; first apply map_union_id_l.
      by split; first apply map_disjoint_empty_l.
    - destruct Happ as [ha [happ [-> [Hdisj [HPa HPapp]]]]].
      apply IHxs in HPapp as [hxs [hys [-> [Hdisj' [HPxs HPys]]]]].
      do 2 eexists. split; first by rewrite (assoc_L (∪)).
      apply map_disjoint_union_r in Hdisj as [].
      split; first by apply map_disjoint_union_l.
      by split; first by do 2 eexists; repeat split.
  + induction xs as [|a xs].
    - induction ys as [|a ys]; intros h [hxs [hys [-> [Hdisj [HPxs HPys]]]]].
      * by inversion HPxs; inversion HPys.
      * simpl; rewrite hiter_cons in *.
        destruct HPys as [ha [hys' [-> [Hdisj' [HPa HPys']]]]].
        apply map_disjoint_union_r in Hdisj as []. exists ha, (hxs ∪ hys').
        split; first by rewrite (assoc_L (∪)), (map_union_comm hxs), (assoc_L (∪)).
        split; first by apply map_disjoint_union_r.
        by split; last by (apply IHys; do 2 eexists; repeat split).
    - intros h [hxs [hys [-> [Hdisj [HPxs HPys]]]]].
      simpl; rewrite hiter_cons in *.
      destruct HPxs as [ha [hxs' [-> [Hdisj' [HPa HPxs']]]]].
      apply map_disjoint_union_l in Hdisj as []. exists ha, (hxs' ∪ hys).
      split; first by rewrite (assoc_L (∪)).
      split; first by apply map_disjoint_union_r.
      by split; last by (apply IHxs; do 2 eexists; repeat split).
Qed.
Lemma hiter_permutation {X : Type} (P : X → asrt) xs ys h :
  xs ≡ₚ ys → hprop h ([∗ xs, P]) ↔ hprop h ([∗ ys, P]).
Proof.
  assert (∀ xs ys, xs ≡ₚ ys → hprop h ([∗ xs, P]) → hprop h ([∗ ys, P])) as H;
    last by intros; split; apply H.
  clear; intros xs ys Hperm. revert h. induction Hperm; intros h Hiter.
  + by intros.
  + rewrite hiter_cons in *. destruct Hiter as [h1 [h2 [-> [Hdisj [HP Hiter]]]]].
    do 2 eexists. repeat split; try done. by apply IHHperm.
  + rewrite hiter_cons in *. destruct Hiter as [hy [hxl [-> [Hdisj [HPy Hiter]]]]].
    rewrite hiter_cons in *. destruct Hiter as [hx [hl [-> [Hdisj' [HPx Hiter]]]]].
    apply map_disjoint_union_r in Hdisj as []. exists hx, (hy ∪ hl).
    split; first by rewrite (assoc_L (∪)), (map_union_comm hy), (assoc_L (∪)).
    split; first by apply map_disjoint_union_r.
    by split; last by (do 2 eexists; repeat split).
  + by apply IHHperm2, IHHperm1.
Qed.
Lemma hiter_submseteq {X : Type} (P : X → asrt) xs ys h :
  ys ⊆+ xs → hprop h ([∗ xs, P]) →
  ∃ h1 h2, h = h1 ∪ h2 ∧ h1 ##ₘ h2 ∧ hprop h1 ([∗ ys, P]).
Proof.
  intros Hsub Hiter. 
  apply submseteq_Permutation in Hsub as [zs Hperm]. eapply hiter_permutation in Hperm.
  apply Hperm, hiter_app in Hiter as [h1 [h2 [-> [Hdisj [Hys Hzs]]]]].
  by do 2 eexists.
Qed.
Lemma elem_of_hiter {X : Type} (P : X → asrt) x xs h :
  x ∈ xs → hprop h ([∗ xs, P]) →
  ∃ h1 h2, h = h1 ∪ h2 ∧ h1 ##ₘ h2 ∧ hprop h1 (P x).
Proof.
  rewrite <- singleton_submseteq_l. intros Hin Hiter.
  specialize (hiter_submseteq _ _ _ _ Hin Hiter) as [? [? [-> [Hdisj HPx]]]].
  rewrite hiter_singleton in HPx. by do 2 eexists.
Qed.

(* Weakening *)
Lemma hempty_weaken P h : hprop h (P ∗ EMP →ₕ P).
Proof. intros [h'[?[->[_[? ->]]]]]. by rewrite <- (map_union_id_r h'). Qed.
Lemma hpure_weaken P Q h : hprop h (P ∗ ⌞ Q ⌟ →ₕ P).
Proof. intros [h'[?[->[_[?[-> _]]]]]]. by rewrite <- (map_union_id_r h'). Qed.
Lemma htrue_weaken P h : hprop h (TRUE ∗ P →ₕ TRUE).
Proof. done. Qed.
Lemma haffine_weaken P Q h : hprop h (⌜ P ⌝ ∗ Q →ₕ ⌜ P ⌝).
Proof. intros [?[?[->[?[? _]]]]]%hstar_assoc. by do 2 eexists. Qed.
