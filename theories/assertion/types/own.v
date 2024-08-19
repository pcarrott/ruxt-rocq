From RUXt.lib Require Import gmap.
From RUXt.lang Require Import semantics.
From RUXt.assertion Require Export types.


Program Definition own (τ : option type) : type := {|
  ty_size := 1;
  ty_own vs := match vs with
               | [VLoc l] => match τ with
                             | Some τ => ∃ₕ v, (PLoc l ↦ PVal v ∗ ⟦τ⟧([v]))
                             | None => PLoc l ↦? ∨ₕ ∃ₕ v, (PLoc l ↦ PVal v)
                             end
               | _ => ⌞ False ⌟
               end
|}.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation.
  intros τ vs h H. destruct vs; first by inversion H.
  destruct v; destruct vs; try by inversion H. eexists.
  destruct τ; simpl in H; first destruct H as [v H].
  all: by split; first apply map_empty_subseteq.
Qed.

Definition empty := own None.
Definition box τ := own (Some τ).
Notation boxes τs := (box <$> τs).

(* Properties *)
Lemma own_uninit h l :
  hprop h (own_type (VLoc l ⊲ empty)) → ∃ v, h = {[l:=v]} ∧ v ≠ Freed.
Proof.
  intros [[? [Hok ->]]|[? [? [? [Hokl [Hokv ->]]]]]].
  + inversion Hok; subst. eexists; by split.
  + inversion Hokl; inversion Hokv; subst. eexists; by split.
Qed.
Lemma own_box h l τ :
  hprop h (own_type (VLoc l ⊲ box τ)) → ∃ v, h !! l = Some (LangVal v).
Proof.
  intros [? [h1 [h2 [-> [Hdisj [[? [v [Hokl [Hokv ->]]]] _]]]]]].
  inversion Hokl; inversion Hokv; subst. eexists.
  rewrite (lookup_union_l _ h2); first apply lookup_singleton.
  by eapply map_disjoint_singleton_l.
Qed.
Lemma own_loc h l τ :
  hprop h (own_type (VLoc l ⊲ own τ)) → ∃ v, h !! l = Some v ∧ v ≠ Freed.
Proof.
  intros Hown. destruct τ.
  + apply own_box in Hown as []. eexists.
    by split.
  + apply own_uninit in Hown as [? [-> ?]]. eexists.
    by split; first apply lookup_singleton.
Qed.
