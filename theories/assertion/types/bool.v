From RUXt.lib Require Import gmap.
From RUXt.assertion Require Export types.


Program Definition bool : type := {|
  ty_size := 1;
  ty_own vs := match vs with
               | [VBool _] => ⌞ True ⌟
               | _ => ⌞ False ⌟
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
  destruct H as [v H]. by split.
Qed.
