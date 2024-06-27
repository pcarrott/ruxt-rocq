From RUXt Require Export lang.


Inductive type :=
| TInt
| TBool
| TOwn (τ : type)
| TPoison
| TProd (τs : list type)
| TSum (τs : list type)
| TCustom (x : string).

Inductive typing := TypedVal (v : val) (τ : type).
Notation "v ⊲ τ" := (TypedVal v τ) (at level 100).

Inductive fun_type := FunType (τs : list type) (τ : type).
Notation "{ τs ↣ τ }" := (FunType τs τ).
Definition type_ctx : Set := gmap string fun_type.

Fixpoint typings (vs : list val) (τs : list type) : option (list typing) :=
  match vs, τs with
  | [], [] => Some []
  | v :: vs, τ :: τs => cons (v ⊲ τ) <$> typings vs τs
  | _, _ => None
  end.

(* TODO *)
Definition interpret (t : typing) : Prop := True.