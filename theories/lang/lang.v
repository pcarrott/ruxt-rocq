From stdpp Require Export binders.
From stdpp Require Import countable.


(* Memory locations *)
Definition block : Set := positive.
Definition loc : Set := block * Z.


(*** Language syntax ***)

(* Language values *)
Inductive val := VInt (z : Z) | VBool (b : bool) | VLoc (l : loc) | VUnit.
(* Language terms *)
Inductive term := Var (x : string) | Val (v : val).
(* Unary operations *)
Inductive un_op := NegOp | NotOp.
(* Binary operations *)
Inductive bin_op := PlusOp | EqOp.
(* Pure expressions *)
Inductive pure :=
| Term (t : term)
| UnOp (op : un_op) (p : pure)
| BinOp (op : bin_op) (p1 p2 : pure).
(* Program expressions *)
Inductive expr :=
| Pure (p : pure)
| Error
| Assume (t : term)
| Let (x : binder) (e1 e2 : expr)
| Choice (e1 e2 : expr)
| Loop (e : expr)
| Alloc
| Free (t : term)
| Store (t1 t2 : term)
| Load (t : term)
| Call (f : string) (ts : list term).

(* Syntactic sugar *)
Notation Vals vs := (Val <$> vs).
Notation PVal v := (Term (Val v)). Notation PVar x := (Term (Var x)).
Notation TInt z := (Val (VInt z)). Notation PInt z := (Term (TInt z)).
Notation TBool b := (Val (VBool b)). Notation PBool b := (Term (TBool b)).
Notation TTrue := (TBool true). Notation PTrue := (Term TTrue).
Notation TFalse := (TBool false). Notation PFalse := (Term TFalse).
Notation TLoc l := (Val (VLoc l)). Notation PLoc l := (Term (TLoc l)).
Notation TUnit := (Val VUnit). Notation PUnit := (Term TUnit).
Notation PNeg p := (UnOp NegOp p). Notation PNot p := (UnOp NotOp p).
Notation PPlus p1 p2 := (BinOp PlusOp p1 p2). Notation PEq p1 p2 := (BinOp EqOp p1 p2).

(* Equality *)
Global Instance value_eq_dec : EqDecision val.
Proof. solve_decision. Defined.
Global Instance term_eq_dec : EqDecision term.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance pure_eq_dec : EqDecision pure.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Defined.

(* Countability *)
Instance value_countable : Countable val.
Proof.
  refine (inj_countable' (λ v, match v with
  | VInt z => (inl (inl z))
  | VBool b => (inl (inr b))
  | VLoc l => (inr (Some l))
  | VUnit => (inr None)
  end) (λ s, match s with
  | (inl (inl z)) => VInt z
  | (inl (inr b)) => VBool b
  | (inr (Some l)) => VLoc l
  | (inr None) => VUnit
  end) _); by intros [].
Qed.
Global Instance term_countable : Countable term.
Proof.
  refine (inj_countable' (λ t, match t with Var x => inl x | Val v => inr v end)
  (λ s, match s with inl x => Var x | inr v => Val v end) _); by intros [].
Qed.
Global Instance un_op_countable : Countable un_op.
Proof.
  refine (inj_countable' (λ op, match op with NegOp => inl () | NotOp => inr () end)
  (λ s, match s with inl () => NegOp | inr () => NotOp end) _); by intros [].
Qed.
Global Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable' (λ op, match op with PlusOp => inl () | EqOp => inr () end)
  (λ s, match s with inl () => PlusOp | inr () => EqOp end) _); by intros [].
Qed.
Global Instance pure_countable : Countable pure.
Proof.
  set (enc :=
    fix go p :=
      match p with
      | Term t => GenLeaf (inl t)
      | UnOp op p => GenNode 0 [GenLeaf (inr (inl op)); go p]
      | BinOp op p1 p2 => GenNode 1 [GenLeaf (inr (inr op)); go p1; go p2]
      end
  ).
  set (dec :=
    fix go p :=
      match p with
      | GenLeaf (inl t) => Term t
      | GenNode 0 [GenLeaf (inr (inl op)); p] => UnOp op (go p)
      | GenNode 1 [GenLeaf (inr (inr op)); p1; p2] => BinOp op (go p1) (go p2)
      | _ => Term (Val VUnit) (* dummy *)
      end).
  refine (inj_countable' enc dec _).
  refine (fix go (p : pure) {struct p} := _ with gov (v : val) {struct v} := _ for go).
  - destruct p as [| |]; simpl; by f_equal.
  - done.
Qed.
Global Instance expr_countable : Countable expr.
Proof. Admitted.


(*** Evaluation ***)

(* Variables *)
Definition eval_term (t : term) : option val :=
  match t with Val v => Some v | Var _ => None end.
(* Unary operations *)
Definition eval_un_op (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, VInt z => Some (VInt (-z))
  | NotOp, VBool b => Some (VBool (negb b))
  | _, _ => None
  end.
(* Binary operations *)
Definition eval_bin_op (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | PlusOp, VInt z1, VInt z2 => Some (VInt (z1 + z2))
  | EqOp, VInt z1, VInt z2 => Some (VBool (Z.eqb z1 z2))
  | _, _, _ => None
  end.
(* Pure expressions *)
Fixpoint eval_pure (p : pure) : option val :=
  match p with
  | Term t => eval_term t
  | UnOp op p => match eval_pure p with Some v => eval_un_op op v | _ => None end
  | BinOp op p1 p2 => match eval_pure p1, eval_pure p2 with
                      | Some v1, Some v2 => eval_bin_op op v1 v2
                      | _, _ => None
                      end
  end.
(* Properties *)
Lemma pure_neg_Some p z :
  eval_pure p = Some (VInt z) → eval_pure (PNeg p) = Some (VInt (-z)).
Proof.
  intros Hok. simpl.
  destruct (eval_pure p); last by exfalso.
  by inversion Hok; subst; simpl.
Qed.
Lemma pure_not_Some p b :
  eval_pure p = Some (VBool b) → eval_pure (PNot p) = Some (VBool (negb b)).
Proof.
  intros Hok. simpl.
  destruct (eval_pure p); last by exfalso.
  by inversion Hok; subst; simpl.
Qed.
Lemma pure_plus_Some p1 p2 z1 z2 :
  eval_pure p1 = Some (VInt z1) → eval_pure p2 = Some (VInt z2) →
  eval_pure (PPlus p1 p2) = Some (VInt (z1 + z2)).
Proof.
  intros Hok1 Hok2. simpl.
  destruct (eval_pure p1); destruct (eval_pure p2); try by exfalso.
  by inversion Hok1; inversion Hok2; subst; simpl.
Qed.
Lemma pure_eq_Some p1 p2 z1 z2 :
  eval_pure p1 = Some (VInt z1) → eval_pure p2 = Some (VInt z2) →
  eval_pure (PEq p1 p2) = Some (VBool (Z.eqb z1 z2)).
Proof.
  intros Hok1 Hok2. simpl.
  destruct (eval_pure p1); destruct (eval_pure p2); try by exfalso.
  by inversion Hok1; inversion Hok2; subst; simpl.
Qed.


(*** Substitution ***)

(* Variables *)
Definition subst_in_term (x : string) (v : val) (t : term) : term :=
  if decide (t = Var x) then Val v else t.
(* Pure expressions *)
Fixpoint subst_in_pure (x : string) (v : val) (p : pure) : pure :=
  match p with
  | Term t => Term (subst_in_term x v t)
  | UnOp op p => UnOp op (subst_in_pure x v p)
  | BinOp op p1 p2 => BinOp op (subst_in_pure x v p1) (subst_in_pure x v p2)
  end.
(* Program expressions *)
Fixpoint subst_in_expr (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Pure p => Pure (subst_in_pure x v p)
  | Error => Error
  | Assume t => Assume (subst_in_term x v t)
  | Let bx e1 e2 => Let bx (subst_in_expr x v e1)
                  (if decide (bx = BNamed x) then e2 else subst_in_expr x v e2)
  | Choice e1 e2 => Choice (subst_in_expr x v e1) (subst_in_expr x v e2)
  | Loop e => Loop (subst_in_expr x v e)
  | Alloc => Alloc
  | Free t => Free (subst_in_term x v t)
  | Store t1 t2 => Store (subst_in_term x v t1) (subst_in_term x v t2)
  | Load t => Load (subst_in_term x v t)
  | Call f ts => Call f (subst_in_term x v <$> ts)
  end.
(* Anonymous substitutions *)
Definition subst (x : binder) (v : val) (e : expr) : expr :=
  match x with BAnon => e | BNamed n => subst_in_expr n v e end.
(* Multiple term substitutions *)
Fixpoint subst_terms (xs : list string) (ts : list term) (e : expr) : option expr :=
  match xs, ts with
  | [], [] => Some e
  | x :: xs, t :: ts => 
    match eval_term t with
    | Some v => (subst_in_expr x v) <$> subst_terms xs ts e
    | _ => None
    end
  | _, _ => None
  end.
(* Multiple value substitutions *)
Definition subst_vals (xs : list string) (vs : list val) (e : expr) : option expr :=
  subst_terms xs (Vals vs) e.


(*** Closed expressions ***)

(* Terms *)
Definition closed_term' (X : list string) (t : term) : Prop :=
  match t with Var x => x ∈ X | Val _ => True end.
Definition closed_term (t : term) : Prop := closed_term' [] t.
(* Pure expressions  *)
Fixpoint closed_pure' (X : list string) (p : pure) : Prop :=
  match p with
  | Term t => closed_term' X t
  | UnOp _ p => closed_pure' X p
  | BinOp _ p1 p2 => closed_pure' X p1 ∧ closed_pure' X p2
  end.
Definition closed_pure (p : pure) : Prop := closed_pure' [] p.
(* Program expressions *)
Fixpoint closed_expr' (X : list string) (e : expr) : Prop :=
  match e with
  | Pure p => closed_pure' X p
  | Error => True
  | Assume t => closed_term' X t
  | Let x e1 e2 => closed_expr' X e1 ∧ closed_expr' (x :b: X) e2
  | Choice e1 e2 => closed_expr' X e1 ∧ closed_expr' X e2
  | Loop e => closed_expr' X e
  | Alloc => True
  | Free t => closed_term' X t
  | Store t1 t2 => closed_term' X t1 ∧ closed_term' X t2
  | Load t => closed_term' X t
  | Call _ ts => Forall (closed_term' X) ts
  end.
Definition closed_expr (e : expr) : Prop := closed_expr' [] e.
