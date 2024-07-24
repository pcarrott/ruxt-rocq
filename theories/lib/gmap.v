From stdpp Require Export gmap.

Section stdpp_extra.
  Context `{FinMapDom K M}.

  Lemma map_disjoint_insert {A} (m1 m2 : M A) i x :
    is_Some (m1 !! i) → m1 ##ₘ m2 → <[i:=x]> m1 ##ₘ m2.
  Proof.
    intros [v HSome] Hdisj. apply map_disjoint_insert_l_2; last done.
    by apply (map_disjoint_Some_l m1 m2 i v).
  Qed.

  Lemma map_union_dom {A} (m1 m2 : M A) i :
    is_Some ((m1 ∪ m2) !! i) → m1 !! i = None → i ∈ dom m2.
  Proof.
    intros HSome HNone. apply elem_of_dom.
    apply lookup_union_is_Some in HSome as [[v HSome]|HSome]; congruence.
  Qed.

  Lemma map_disjoint_union_insert {A} (m1 m2 : M A) i x :
    m1 ##ₘ m2 → i ∉ dom (m1 ∪ m2) → <[i:=x]> m1 ##ₘ m2.
  Proof.
    intros Hdisj Hnin. apply map_disjoint_insert_l_2; last done.
    apply not_elem_of_dom. intros Hin.
    apply Hnin, dom_union, elem_of_union. by right.
  Qed.

  Lemma map_union_id_left {A} (m : M A) : m = ∅ ∪ m.
  Proof. rewrite left_id; first done; apply map_empty_union. Qed.
  Lemma map_union_id_right {A} (m : M A) : m = m ∪ ∅.
  Proof. rewrite right_id; first done; apply map_union_empty. Qed.
End stdpp_extra.