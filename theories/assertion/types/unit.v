From RUXt.lib Require Import gmap.
From RUXt.assertion Require Export types.


Program Definition unit : type := {|
  ty_size := 1;
  ty_own vs := match vs with
               | [VUnit] => ⌜ True ⌝
               | _ => ⌜ False ⌝
               end
|}.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation.
  intros vs h H. destruct vs; first by inversion H.
  destruct v; destruct vs; try by inversion H. eexists.
  destruct H as [v H]. split; first done. subst; apply map_empty_subseteq.
Qed.
