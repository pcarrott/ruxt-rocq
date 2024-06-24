From stdpp Require Export strings.
From stdpp Require Import gmap.

Definition block : Set := positive.
Definition loc : Set := block * Z.

Declare Scope loc_scope.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, (l.2 + z)%Z).
Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.

Inductive val := ValInt (n : Z) | ValLoc (l : loc) | ValBool (b : bool) | ValUnit.

Inductive bin_op := PlusOp | MinusOp | LeOp | EqOp | OffsetOp.

Inductive pure :=
| Val (l : val)
| Var (x : string)
| BinOp (op : bin_op) (p1 p2 : pure).

Inductive binder := BAnon | BNamed : string → binder.

Inductive expr :=
| Pure (p : pure)
| Error
| Assume (p : pure)
| Let (x : binder) (e1 e2 : expr)
| Choice (e1 e2 : expr)
| Loop (e : expr)
| Alloc
| Free (p : pure)
| Store (p1 p2 : pure)
| Load (p : pure)
| FunCall (f : string) (p : list pure).

Inductive error := ErrBot.

Inductive exit := Ok (l : val) | Err (e : error) | Miss (l : loc).

Definition eval_binop (op : bin_op) (l1 l2 : val) : exit :=
    match op, l1, l2 with
    | PlusOp, ValInt z1, ValInt z2 => Ok (ValInt (z1 + z2))
    | MinusOp, ValInt z1, ValInt z2 => Ok (ValInt (z1 - z2))
    | LeOp, ValInt z1, ValInt z2 => Ok (ValBool (Z.leb z1 z2))
    | EqOp, ValInt z1, ValInt z2 => Ok (ValBool (Z.eqb z1 z2))
    | OffsetOp, ValLoc l1, ValInt z2 => Ok (ValLoc (l1 +ₗ z2))
    | _, _, _ => Err ErrBot
    end.

Fixpoint eval_pure (p : pure) : exit :=
    match p with
    | Val l => Ok l
    | Var x => Err ErrBot
    | BinOp op p1 p2 => 
        match eval_pure p1, eval_pure p2 with
        | Ok l1, Ok l2 => eval_binop op l1 l2
        | _, _ => Err ErrBot
        end
    end.

Definition heap := gmap loc val.