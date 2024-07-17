From RUXt.assertion Require Export types.
From RUXt.lib Require Import gmap.


Program Definition int : type := {|
  ty_size := 1;
  ty_own vs := match vs with
               | [VInt _] => ⌜ True ⌝
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
  destruct v; destruct vs; try by inversion H. exists ∅.
  destruct H as [v H]. split; first done. apply map_empty_subseteq.
Qed.
