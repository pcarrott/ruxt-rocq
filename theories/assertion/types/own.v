From RUXt.lib Require Import gmap.
From RUXt.assertion Require Export types.


Program Definition own (τ : option type) : type := {|
  ty_size := 1;
  ty_own vs := match vs with
               | [VLoc l] => match τ with
                             | Some τ => ∃∃ v, (PLoc l ↦ PVal v ∗ ⟦τ⟧([v]))
                             | None => PLoc l ↦?
                             end
               | _ => ⌜ False ⌝
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
  all: split; first done; subst; apply map_empty_subseteq.
Qed.

Definition uninit := own None.
Definition box τ := own (Some τ).
Notation boxes τs := (box <$> τs).