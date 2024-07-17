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
Inductive typing := TyOwned (v : val) (τ : type).
Notation "v ⊲ τ" := (TyOwned v τ) (at level 100).

(* Assign types from lists *)
Fixpoint to_typing (vs : list val) (τs : list type) : option (list typing) :=
  match vs, τs with
  | [], [] => Some []
  | v :: vs, τ :: τs => cons (v ⊲ τ) <$> to_typing vs τs
  | _, _ => None
  end.

(* Type interpretation *)
Definition own_type (t : typing) : hprop :=
  match t with
  | v ⊲ τ => ⟦τ⟧([v])
  end.
Fixpoint interpret (𝕋 : list typing) : hprop :=
  match 𝕋 with
  | [] => emp
  | t :: 𝕋 => own_type t ∗ interpret 𝕋
  end.
Notation "'[∗' 𝕋 ]" := (interpret 𝕋).