From RUXt.lang Require Export lang.
From RUXt.assertion Require Export hprop.


(*** Type system ***)
(* TODO: Handle (mut/shr) references and lifetimes *)
(* TODO: Define default types *)

(* Language types *)
Record type := {
  ty_size : nat;
  ty_own : list val → hprop;
  ty_size_eq vs : ty_own vs ⊢ ⌜ length vs = ty_size ⌝;
}.
Notation "⟦ τ '⟧(' vs )" := (ty_own τ vs).

(* Type assignment *)
Inductive typing := TyOwn (v : val) (τ : type).
Notation "v ⊲ τ" := (TyOwn v τ) (at level 50).
Notation "vs [⊲] τs" := (zip_with TyOwn vs τs) (at level 50).

(* Type interpretation *)
Definition own_type (t : typing) : hprop :=
  match t with
  | v ⊲ τ => ⟦τ⟧([v])
  end.
Notation "'[∗' 𝕋 ]" := ([∗ 𝕋, own_type]).
