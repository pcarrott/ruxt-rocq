From stdpp Require Export list.

Section more_general_properties.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.

  Lemma Permutation_spec l1 l2 :
    l1 ≡ₚ l2 → ∀ x, x ∈ l1 ↔ x ∈ l2.
  Proof.
    intros Hperm x. split; intros Hin.
    + apply elem_of_Permutation in Hin as [? Hcons].
      rewrite Hcons in Hperm.
      apply Permutation_cons_inv_l in Hperm as [? [? [-> _]]].
      apply elem_of_app; right. by left.
    + apply elem_of_Permutation in Hin as [? Hcons].
      rewrite Hcons in Hperm.
      apply Permutation_cons_inv_r in Hperm as [? [? [-> _]]].
      apply elem_of_app; right. by left.
  Qed.
End more_general_properties.

Section subseteq.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.

  Lemma elem_of_subseteq l k x : x ∈ l → l ⊆ k → x ∈ k.
  Proof.
    intros Hin Hsub. induction l; first inversion Hin.
    apply list_subseteq_cons_iff in Hsub as [].
    by apply elem_of_cons in Hin as [<-|]; last apply IHl.
  Qed.
End subseteq.

Section zip_with.
  Context {A B C : Type} (f : A → B → C).
  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma zip_with_reverse l k :
    length l = length k →
    zip_with f l k ≡ₚ zip_with f (reverse l) (reverse k).
  Proof.
    rewrite <- Forall2_same_length. induction 1; f_equal/=; auto.
    rewrite IHForall2, 2 reverse_cons, zip_with_app;
      last by rewrite 2 length_reverse, <- Forall2_same_length.
    by apply Permutation_cons_append.
  Qed.
End zip_with.
