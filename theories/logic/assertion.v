From RUXt.lang Require Import semantics.
From RUXt.lib Require Import gmap.


(*** Assertion language ***)

(* Assertion syntax *)
Inductive asrt :=
| A_PureEq (p1 p2 : pure)
| A_PureTrue (p : pure)
| A_Emp
| A_Points (p1 p2 : pure)
| A_Freed (p : pure)
| A_Uninit (p : pure)
| A_False
| A_Implies (a1 a2 : asrt)
| A_Exists (x : string) (a : asrt)
| A_SubstV (a : asrt) (x : string) (v : value)
| A_SubstX (a : asrt) (x y : string)
| A_Star (a1 a2 : asrt).
(* Syntactic sugar *)
Notation A_Not a := (A_Implies a A_False).
Notation A_True := (A_Not A_False).
Notation A_Or a1 a2 := (A_Implies (A_Not a1) a2).
Notation A_And a1 a2 := (A_Not (A_Implies a1 (A_Not a2))).
(* Logical variable substitution *)
Definition sub := gmap string value.
Fixpoint subst_pure' (θ : sub) (p : pure) : pure :=
  match p with
  | Val v => Val v
  | Var x => match θ !! x with Some v => Val v | None => Var x end
  | UnOp op p => UnOp op (subst_pure' θ p)
  | BinOp op p1 p2 => BinOp op (subst_pure' θ p1) (subst_pure' θ p2)
  end.
Definition pure_to_exit' (θ : sub) (p : pure) : exit := pure_to_exit (subst_pure' θ p).
(* Assertion satisfiability *)
Fixpoint eval_asrt (θ : sub) (h : heap) (a : asrt) : Prop :=
  match a with
  | A_PureEq p1 p2 =>
    h = ∅ ∧ ∃ v, pure_to_exit' θ p1 = Ok v ∧ pure_to_exit' θ p1 = pure_to_exit' θ p2
  | A_PureTrue p =>
    h = ∅ ∧ pure_to_exit' θ p = Ok (VBool true)
  | A_Emp =>
    h = ∅
  | A_Points p1 p2 =>
    ∃ l v, pure_to_exit' θ p1 = Ok (VLoc l) ∧ pure_to_exit' θ p2 = Ok v ∧ h = {[l := LangVal v]}
  | A_Freed p =>
    ∃ l, pure_to_exit' θ p = Ok (VLoc l) ∧ h = {[l := Freed]}
  | A_Uninit p =>
    ∃ l, pure_to_exit' θ p = Ok (VLoc l) ∧ h = {[l := Poison]}
  | A_False =>
    False
  | A_Implies a1 a2 =>
    eval_asrt θ h a1 → eval_asrt θ h a2
  | A_Exists x a =>
    ∃ v, eval_asrt (<[x:=v]> θ) h a
  | A_SubstV a x v =>
    eval_asrt (<[x:=v]> θ) h a
  | A_SubstX a x y =>
    ∃ v, θ !! y = Some v ∧ eval_asrt (<[x:=v]> θ) h a
  | A_Star a1 a2 =>
    ∃ h1 h2, h = h1 ∪ h2 ∧ h1 ##ₘ h2 ∧ eval_asrt θ h1 a1 ∧ eval_asrt θ h2 a2
  end.
Definition assert (a : asrt) : Prop := ∀ h θ, eval_asrt θ h a.


(*** Language types ***)
(* TODO: Handle (mut/shr) references and lifetimes *)
(* TODO: Define default types *)

(* Language types *)
Record type := {
  ty_size : nat;
  ty_own : list value → asrt;
  ty_size_eq vs : assert (ty_own vs) → length vs = ty_size;
}.
Notation "⟦ τ '⟧(' vs )" := (ty_own τ vs).
(* Type assignment *)
Inductive typing := TyOwned (v : value) (τ : type).
Notation "v ⊲ τ" := (TyOwned v τ) (at level 100).
(* Assign types from lists *)
Fixpoint to_typing (vs : list value) (τs : list type) : option (list typing) :=
  match vs, τs with
  | [], [] => Some []
  | v :: vs, τ :: τs => cons (v ⊲ τ) <$> to_typing vs τs
  | _, _ => None
  end.
(* Type interpretation *)
Definition own_type (t : typing) : asrt :=
  match t with
  | v ⊲ τ => ⟦τ⟧([v])
  end.
Fixpoint interpret (𝕋 : list typing) : asrt :=
  match 𝕋 with
  | [] => A_Emp
  | t :: 𝕋 => A_Star (own_type t) (interpret 𝕋)
  end.
Notation "[∗ 𝕋 ]" :=
  (interpret 𝕋) (at level 0).
