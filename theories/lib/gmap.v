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
End stdpp_extra.