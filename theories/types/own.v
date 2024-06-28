From RUXt.lang Require Import lang.
From RUXt.logic Require Import assertion.


(* TODO: Properly define this *)
Program Definition own_ptr (τ : type) : type := {|
  ty_size := 1;
  ty_own vs := 
    match vs with
    | [VLoc l] => A_Exists "v" (A_Points (Val (VLoc l)) (Var "v"))
    | _ => A_False
    end
|}.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation. by intros. Qed.
Next Obligation.
  simpl. intros τ vs H. specialize (H ∅ ∅).
  destruct vs; first by exfalso.
  destruct v; by destruct vs.
Qed.