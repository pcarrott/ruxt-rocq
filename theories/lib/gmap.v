From stdpp Require Export binders.
From stdpp Require Export gmap.
From RUXt.lib Require Export list.

Section stdpp_extra.
  Context `{FinMapDom K M} `{A}.
  Implicit Types m : M A.

  Lemma map_disjoint_insert_singleton_l m i x y z :
    <[i:=x]> {[i := y]} ##ₘ m ↔ {[i := z]} ##ₘ m.
  Proof.
    rewrite map_disjoint_insert_l, 2 map_disjoint_singleton_l.
    by split; first by intros [].
  Qed.
  Lemma map_disjoint_insert_singleton_r m i x y z :
    m ##ₘ <[i:=x]> {[i := y]} ↔ m ##ₘ {[i := z]}.
  Proof.
    rewrite map_disjoint_insert_r, 2 map_disjoint_singleton_r.
    by split; first by intros [].
  Qed.

  Lemma map_disjoint_Some_insert m1 m2 i x y :
    m1 !! i = Some x → m1 ##ₘ m2 → <[i:=y]> m1 ##ₘ m2.
  Proof.
    intros. by apply map_disjoint_insert_l_2; first eapply map_disjoint_Some_l.
  Qed.

  Lemma map_union_dom m1 m2 i :
    is_Some ((m1 ∪ m2) !! i) → m1 !! i = None → i ∈ dom m2.
  Proof.
    intros HSome HNone. apply elem_of_dom.
    apply lookup_union_is_Some in HSome as [[v HSome]|HSome]; congruence.
  Qed.

  Lemma map_disjoint_union_insert m1 m2 i x :
    m1 ##ₘ m2 → i ∉ dom (m1 ∪ m2) → <[i:=x]> m1 ##ₘ m2.
  Proof.
    intros Hdisj Hnin. apply map_disjoint_insert_l_2; last done.
    apply not_elem_of_dom. intros Hin.
    apply Hnin, dom_union, elem_of_union. by right.
  Qed.

  Lemma map_union_id_l m : m = ∅ ∪ m.
  Proof. rewrite left_id; first done; apply map_empty_union. Qed.
  Lemma map_union_id_r m : m = m ∪ ∅.
  Proof. rewrite right_id; first done; apply map_union_empty. Qed.
End stdpp_extra.
