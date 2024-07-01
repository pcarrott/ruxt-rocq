From stdpp Require Export binders.


(* Memory locations *)
Definition block : Set := positive.
Definition loc : Set := block * Z.


(*** Language syntax ***)

(* Language values *)
Inductive value := VInt (z : Z) | VLoc (l : loc) | VBool (b : bool) | VUnit.
(* Unary operations *)
Inductive un_op := NotOp.
(* Binary operations *)
Inductive bin_op := PlusOp | EqOp.
(* Pure expressions *)
Inductive pure :=
| Val (v : value)
| Var (x : string)
| UnOp (op : un_op) (p : pure)
| BinOp (op : bin_op) (p1 p2 : pure).
(* Language expressions *)
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
| Call (f : string) (ps : list pure).
(* Syntactic sugar *)
Notation If p e1 e2 := (Choice (Let BAnon (Assume p) e1) (Let BAnon (Assume (UnOp NotOp p)) e2)).
Notation While p e := (Let BAnon (Loop (Let BAnon (Assume p) e)) (Assume (UnOp NotOp p))).
Notation Assert p := (Choice (Assume p) (Let BAnon (Assume (UnOp NotOp p)) Error)).


(*** Evaluation ***)

(* Unary operations *)
Definition eval_un_op (op : un_op) (v : value) : option value :=
  match op, v with
  | NotOp, VBool b => Some (VBool (negb b))
  | _, _ => None
  end.
(* Binary operations *)
Definition eval_bin_op (op : bin_op) (v1 v2 : value) : option value :=
  match op, v1, v2 with
  | PlusOp, VInt z1, VInt z2 => Some (VInt (z1 + z2))
  | EqOp, VInt z1, VInt z2 => Some (VBool (Z.eqb z1 z2))
  | _, _, _ => None
  end.
(* Pure expressions *)
Fixpoint eval_pure (p : pure) : option value :=
  match p with
  | Val v => Some v
  | Var x => None
  | UnOp op p =>
    match eval_pure p with
    | Some v => eval_un_op op v
    | _ => None
    end
  | BinOp op p1 p2 => 
    match eval_pure p1, eval_pure p2 with
    | Some v1, Some v2 => eval_bin_op op v1 v2
    | _, _ => None
    end
  end.


(*** Variable substitution ***)

(* Pure expressions *)
Fixpoint subst_pure (x : string) (v : value) (p : pure) : pure :=
  match p with
  | Val v => Val v
  | Var y => if decide (x = y) then Val v else p
  | UnOp op p => UnOp op (subst_pure x v p)
  | BinOp op p1 p2 => BinOp op (subst_pure x v p1) (subst_pure x v p2)
  end.
(* Language expressions *)
Fixpoint subst_expr (x : string) (v : value) (e : expr) : expr :=
  match e with
  | Pure p => Pure (subst_pure x v p)
  | Error => Error
  | Assume p => Assume (subst_pure x v p)
  | Let y e1 e2 => if decide (y = BNamed x) then Let y (subst_expr x v e1) e2
                   else Let y (subst_expr x v e1) (subst_expr x v e2)
  | Choice e1 e2 => Choice (subst_expr x v e1) (subst_expr x v e2)
  | Loop e => Loop (subst_expr x v e)
  | Alloc => Alloc
  | Free p => Free (subst_pure x v p)
  | Store p1 p2 => Store (subst_pure x v p1) (subst_pure x v p2)
  | Load p => Load (subst_pure x v p)
  | Call f ps => Call f (subst_pure x v <$> ps)
  end.
(* Anonymous binders *)
Definition subst (x : binder) (v : value) (e : expr) : expr :=
  match x with BAnon => e | BNamed n => subst_expr n v e end.
(* Multiple pure substitutions *)
Fixpoint subst_l_pure (xs : list string) (ps : list pure) (e : expr) : option expr :=
  match xs, ps with
  | [], [] => Some e
  | x :: xs, p :: ps => 
    match eval_pure p with
    | Some v => (subst_expr x v) <$> subst_l_pure xs ps e
    | _ => None
    end
  | _, _ => None
  end.
(* Multiple value substitutions *)
Definition subst_l (xs : list string) (vs : list value) (e : expr) : option expr :=
  subst_l_pure xs (Val <$> vs) e.
