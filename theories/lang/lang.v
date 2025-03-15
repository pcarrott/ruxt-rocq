From stdpp Require Export binders.
From stdpp Require Import countable.
From RUXt.lib Require Import list gmap.


(* Memory locations *)
Definition block : Set := positive.
Definition loc : Set := block * nat.
Definition offset (l : loc) (i : nat) : loc := (l.1, l.2 + i).
Notation "l +ₗ i" := (offset l i) (at level 50).
(* Properties *)
Lemma offset_0 l : l +ₗ 0 = l.
Proof. unfold offset. rewrite Nat.add_0_r. by destruct l. Qed.


(*** Language syntax ***)

(* Language values *)
Inductive val := VInt (z : Z) | VBool (b : bool) | VLoc (l : loc) | VUnit.
(* Language terms *)
Inductive term := TVar (x : string) | TVal (v : val).
(* Unary operations *)
Inductive un_op := MinusOp | NotOp.
(* Binary operations *)
Inductive bin_op := AddOp | LeOp | OffsetOp.
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
| Alloc (t : term)
| Free (t : term)
| Store (t1 t2 : term)
| Load (t : term)
| Call (f : string) (ts : list term).

(* Syntactic sugar *)
Notation TVals vs := (TVal <$> vs).
Notation TVars vs := (TVar <$> vs).
Notation PVal v := (Term (TVal v)). Notation PVar x := (Term (TVar x)).
Notation TInt z := (TVal (VInt z)). Notation PInt z := (Term (TInt z)).
Notation TBool b := (TVal (VBool b)). Notation PBool b := (Term (TBool b)).
Notation TTrue := (TBool true). Notation PTrue := (Term TTrue).
Notation TFalse := (TBool false). Notation PFalse := (Term TFalse).
Notation TLoc l := (TVal (VLoc l)). Notation PLoc l := (Term (TLoc l)).
Notation TUnit := (TVal VUnit). Notation PUnit := (Term TUnit).
Notation PMinus p := (UnOp MinusOp p). Notation PNot p := (UnOp NotOp p).
Notation PAdd p1 p2 := (BinOp AddOp p1 p2). Notation PLe p1 p2 := (BinOp LeOp p1 p2).
Notation POffset p1 p2 := (BinOp OffsetOp p1 p2).

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
  refine (inj_countable' (λ t, match t with TVar x => inl x | TVal v => inr v end)
  (λ s, match s with inl x => TVar x | inr v => TVal v end) _); by intros [].
Qed.
Global Instance un_op_countable : Countable un_op.
Proof.
  refine (inj_countable' (λ op, match op with MinusOp => inl () | NotOp => inr () end)
  (λ s, match s with inl () => MinusOp | inr () => NotOp end) _); by intros [].
Qed.
Global Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable'
    (λ op, 
      match op with
      | AddOp => inl ()
      | LeOp => inr (inl ())
      | OffsetOp => inr (inr ())
      end
    )
    (λ s,
      match s with
      | inl () => AddOp
      | inr (inl ()) => LeOp
      | inr (inr ()) => OffsetOp end
    )
    _
  ); by intros [].
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
      | _ => Term (TVal VUnit) (* dummy *)
      end).
  refine (inj_countable' enc dec _).
  refine (fix go (p : pure) {struct p} := _ with gov (v : val) {struct v} := _ for go).
  - destruct p as [| |]; simpl; by f_equal.
  - done.
Qed.
Global Instance expr_countable : Countable expr.
Proof.
  set (enc :=
    fix go e :=
      match e with
      | Pure p => GenLeaf (inl (Some p))
      | Error => GenLeaf (inl None)
      | Let x e1 e2 => GenNode 0 [GenLeaf (inr (inl x)); go e1; go e2]
      | Choice e1 e2 => GenNode 1 [go e1; go e2]
      | Assume t => GenLeaf (inr (inr (inr (inl t))))
      | Call f ts => GenNode 2 [
          GenLeaf (inr (inr (inr (inr (inl f)))));
          GenLeaf (inr (inr (inr (inr (inr ts)))))
        ]
      | Alloc t => GenLeaf (inr (inr (inl (inl (inl t)))))
      | Free t => GenNode 3 [
          GenLeaf (inr (inr (inl (inl (inr t)))))
        ]
      | Store t1 t2 => GenNode 4 [
          GenLeaf (inr (inr (inl (inr (inl (inl t1))))));
          GenLeaf (inr (inr (inl (inr (inl (inr t2))))))
        ]
      | Load t => GenLeaf (inr (inr (inl (inr (inr t)))))
      end
  ).
  set (dec :=
    fix go e :=
      match e with
      | GenLeaf (inl (Some p)) => Pure p
      | GenLeaf (inl None) => Error
      | GenNode 0 [GenLeaf (inr (inl x)); e1; e2] => Let x (go e1) (go e2)
      | GenNode 1 [e1; e2] => Choice (go e1) (go e2)
      | GenLeaf (inr (inr (inr (inl t)))) => Assume t
      | GenNode 2 [
          GenLeaf (inr (inr (inr (inr (inl f)))));
          GenLeaf (inr (inr (inr (inr (inr ts)))))
        ] => Call f ts
      | GenLeaf (inr (inr (inl (inl (inl t))))) => Alloc t
      | GenNode 3 [
          GenLeaf (inr (inr (inl (inl (inr t)))))
        ] => Free t
      | GenNode 4 [
          GenLeaf (inr (inr (inl (inr (inl (inl t1))))));
          GenLeaf (inr (inr (inl (inr (inl (inr t2))))))
        ] => Store t1 t2
      | GenLeaf (inr (inr (inl (inr (inr t))))) => Load t
      | _ => Error (* dummy *)
      end).
  refine (inj_countable' enc dec _).
  refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
  - destruct e as [| | | | | | | | |]; simpl; by f_equal.
  - done.
Qed.


(*** Evaluation ***)

(* Terms *)
Definition eval_term (t : term) : option val :=
  match t with TVal v => Some v | TVar _ => None end.
Notation "⌊ t ⌋ₜ" := (eval_term t) (at level 50).
(* Unary operations *)
Definition eval_un_op (op : un_op) (v : val) : option val :=
  match op, v with
  | MinusOp, VInt z => Some (VInt (-z))
  | NotOp, VBool b => Some (VBool (negb b))
  | _, _ => None
  end.
(* Binary operations *)
Definition eval_bin_op (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | AddOp, VInt z1, VInt z2 => Some (VInt (z1 + z2))
  | LeOp, VInt z1, VInt z2 => Some (VBool (Z.leb z1 z2))
  | OffsetOp, VLoc l, VInt z => Some (VLoc (l +ₗ (Z.to_nat z)))
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
Notation "⌊ p ⌋ₚ" := (eval_pure p) (at level 50).

(* Properties *)
Lemma pure_neg_Some p z :
  ⌊ p ⌋ₚ = Some (VInt z) → ⌊ PMinus p ⌋ₚ = Some (VInt (-z)).
Proof.
  intros Hok. simpl.
  destruct (eval_pure p); last by exfalso.
  by inversion Hok; subst; simpl.
Qed.
Lemma pure_not_Some p b :
  ⌊ p ⌋ₚ = Some (VBool b) → ⌊ PNot p ⌋ₚ = Some (VBool (negb b)).
Proof.
  intros Hok. simpl.
  destruct (eval_pure p); last by exfalso.
  by inversion Hok; subst; simpl.
Qed.
Lemma pure_plus_Some p1 p2 z1 z2 :
  ⌊ p1 ⌋ₚ = Some (VInt z1) → ⌊ p2 ⌋ₚ = Some (VInt z2) →
  ⌊ PAdd p1 p2 ⌋ₚ = Some (VInt (z1 + z2)).
Proof.
  intros Hok1 Hok2. simpl.
  destruct (eval_pure p1); destruct (eval_pure p2); try by exfalso.
  by inversion Hok1; inversion Hok2; subst; simpl.
Qed.
Lemma pure_le_Some p1 p2 z1 z2 :
  ⌊ p1 ⌋ₚ = Some (VInt z1) → ⌊ p2 ⌋ₚ = Some (VInt z2) →
  ⌊ PLe p1 p2 ⌋ₚ = Some (VBool (Z.leb z1 z2)).
Proof.
  intros Hok1 Hok2. simpl.
  destruct (eval_pure p1); destruct (eval_pure p2); try by exfalso.
  by inversion Hok1; inversion Hok2; subst; simpl.
Qed.
Lemma pure_offset_Some p1 p2 l z :
  ⌊ p1 ⌋ₚ = Some (VLoc l) → ⌊ p2 ⌋ₚ = Some (VInt z) →
  ⌊ POffset p1 p2 ⌋ₚ = Some (VLoc (l +ₗ (Z.to_nat z))).
Proof.
  intros Hok1 Hok2. simpl.
  destruct (eval_pure p1); destruct (eval_pure p2); try by exfalso.
  by inversion Hok1; inversion Hok2; subst; simpl.
Qed.


(*** Substitution and closed expressions ***)

(* Terms *)
Definition closed_term (X : gset string) (t : term) : Prop :=
  match t with TVar x => x ∈ X | TVal _ => True end.
Definition subst_in_term (x : string) (t : term) (T : term) : term :=
  if decide (T = TVar x) then t else T.
(* Pure expressions  *)
Fixpoint closed_pure (X : gset string) (p : pure) : Prop :=
  match p with
  | Term t => closed_term X t
  | UnOp _ p => closed_pure X p
  | BinOp _ p1 p2 => closed_pure X p1 ∧ closed_pure X p2
  end.
Fixpoint subst_in_pure (x : string) (t : term) (p : pure) : pure :=
  match p with
  | Term T => Term (subst_in_term x t T)
  | UnOp op p => UnOp op (subst_in_pure x t p)
  | BinOp op p1 p2 => BinOp op (subst_in_pure x t p1) (subst_in_pure x t p2)
  end.
(* Program expressions *)
Fixpoint closed_expr (X : gset string) (e : expr) : Prop :=
  match e with
  | Pure p => closed_pure X p
  | Error => True
  | Assume t => closed_term X t
  | Let bx e1 e2 => closed_expr X e1 ∧
                    closed_expr (match bx with BAnon => X | BNamed x => X ∪ {[x]} end) e2
  | Choice e1 e2 => closed_expr X e1 ∧ closed_expr X e2
  | Alloc t => closed_term X t
  | Free t => closed_term X t
  | Store t1 t2 => closed_term X t1 ∧ closed_term X t2
  | Load t => closed_term X t
  | Call _ ts => Forall (closed_term X) ts
  end.
Definition closed_program (e : expr) : Prop := closed_expr ∅ e.
Fixpoint subst_in_expr (x : string) (t : term) (e : expr) : expr :=
  match e with
  | Pure p => Pure (subst_in_pure x t p)
  | Error => Error
  | Assume T => Assume (subst_in_term x t T)
  | Let bx e1 e2 => Let bx (subst_in_expr x t e1)
                    (if decide (bx = BNamed x) then e2 else subst_in_expr x t e2)
  | Choice e1 e2 => Choice (subst_in_expr x t e1) (subst_in_expr x t e2)
  | Alloc T => Alloc (subst_in_term x t T)
  | Free T => Free (subst_in_term x t T)
  | Store T1 T2 => Store (subst_in_term x t T1) (subst_in_term x t T2)
  | Load T => Load (subst_in_term x t T)
  | Call f Ts => Call f (subst_in_term x t <$> Ts)
  end.
Definition subst (bx : binder) (v : val) (e : expr) : expr :=
  match bx with BAnon => e | BNamed x => subst_in_expr x (TVal v) e end.
Definition subst_terms (xs : list string) (ts : list term) (e : expr) : expr :=
  foldl (λ e xt, subst_in_expr xt.1 xt.2 e) e (zip xs ts).

(* Syntactic sugar *)
Notation "e ⌊ v // x ⌋" := (subst x v e) (at level 50).
Notation "e ⌊ ts [//] xs ⌋ₜ" := (subst_terms xs ts e) (at level 50).
Notation "e ⌊ vs [//] xs ⌋" := (subst_terms xs (TVals vs) e) (at level 50).


(* Properties *)
Lemma is_closed_term X T : closed_term X T → ∀ x t, x ∉ X → subst_in_term x t T = T.
Proof.
  intros Hclosed. destruct T.
  + intros. simpl in Hclosed. unfold subst_in_term.
    by case_decide as Heq; first congruence.
  + intros. unfold subst_in_term. by case_decide.
Qed.
Lemma is_closed_pure X p : closed_pure X p → ∀ x t, x ∉ X → subst_in_pure x t p = p.
Proof.
  intros Hclosed. induction p; intros; simpl.
  + by rewrite (is_closed_term X).
  + by rewrite IHp.
  + destruct Hclosed as [Hclosed1 Hclosed2].
    by rewrite IHp1, IHp2.
Qed.
Lemma is_closed_expr X e : closed_expr X e → ∀ x t, x ∉ X → subst_in_expr x t e = e.
Proof.
  generalize dependent X. induction e; intros X Hclosed x' t' Hnin; simpl in *.
  + by rewrite (is_closed_pure X).
  + done.
  + by rewrite (is_closed_term X).
  + destruct Hclosed as [Hclosed1 Hclosed2].
    rewrite (IHe1 X); try done. case_decide; first done.
    destruct x as [|x].
    - by rewrite (IHe2 X).
    - rewrite (IHe2 (X ∪ {[x]})); try done.
      apply not_elem_of_union. split; first done.
      apply not_elem_of_singleton. congruence.
  + destruct Hclosed as [Hclosed1 Hclosed2].
    by rewrite (IHe1 X), (IHe2 X).
  + by rewrite (is_closed_term X).
  + by rewrite (is_closed_term X).
  + destruct Hclosed as [Hclosed1 Hclosed2].
    by rewrite 2 (is_closed_term X).
  + by rewrite (is_closed_term X).
  + rewrite <- (Forall_fmap_ext_1 id), list_fmap_id; first done.
    apply Forall_forall. intros ? Hin.
    eapply Forall_forall in Hin; last done.
    by rewrite (is_closed_term X).
Qed.
Lemma is_closed_program e : closed_program e → ∀ x v, e ⌊ v // x ⌋ = e.
Proof.
  intros. unfold subst. destruct x; first done.
  eapply is_closed_expr; try done; inversion 1.
Qed.
Lemma subst_vals_subst e xs vs x v :
  length xs = length vs →
  (e⌊ vs [//] xs ⌋)⌊ v // BNamed x ⌋ = e⌊ vs ++ [v] [//] xs ++ [x] ⌋.
Proof.
  intros Hlen. unfold subst_terms.
  rewrite fmap_app, zip_with_app, foldl_app; solve_length.
Qed.
Lemma subst_TVals x v (vs : list val) :
  subst_in_term x v <$> TVals vs = TVals vs.
Proof.
  induction vs; first done.
  simpl. unfold subst_in_term in *.
  unfold TVals in IHvs. rewrite IHvs.
  by case_decide.
Qed.
Lemma subst_TVars x v (xs : list string) :
  x ∉ xs → subst_in_term x v <$> TVars xs = TVars xs.
Proof.
  induction xs; first done. intros Hnin.
  simpl. unfold subst_in_term in *.
  unfold TVars in IHxs. rewrite IHxs; last first.
  { intros Hin. apply Hnin. apply elem_of_cons. by right. }
  case_decide; last done. exfalso.
  apply Hnin. apply elem_of_cons. left. congruence.
Qed.
Lemma subst_call_args f xs vs :
  length xs = length vs → NoDup xs →
  Call f (TVars xs) ⌊ vs [//] xs ⌋ = Call f (TVals vs).
Proof.
  assert (
    ∀ vs1 vs2, vs = vs1 ++ vs2 → length xs = length vs2 → NoDup xs →
    Call f (TVals vs1 ++ TVars xs) ⌊ vs2 [//] xs ⌋ = Call f (TVals vs)
  ) as Hcall.
  {
    induction xs as [|x xs]; intros vs1 vs2 Hvs Hlen Hdup.
    + symmetry in Hlen; apply nil_length_inv in Hlen; subst.
      by rewrite fmap_app.
    + destruct vs2 as [|v vs2]; first inversion Hlen.
      rewrite 2 length_cons in Hlen.
      assert (length xs = length vs2) as Hlen' by lia.
      apply NoDup_cons in Hdup as [Hnin Hdup].
      rewrite cons_middle, app_assoc in Hvs.
      specialize (IHxs (vs1 ++ [v]) vs2 Hvs Hlen' Hdup) as <-.
      rewrite fmap_app, <- app_assoc.
      unfold TVars, subst_terms.
      simpl; rewrite fmap_app, subst_TVals.
      rewrite fmap_cons, subst_TVars; last done.
      unfold subst_in_term; by case_decide.
  }
  assert (vs = [] ++ vs) as Hvs by done.
  specialize (Hcall [] vs Hvs).
  intros Hlen Hdup. by apply Hcall.
Qed.
Lemma let_subst x xs vs e1 e2 :
  length xs = length vs → x ∉ xs → closed_program e1 →
  (Let (BNamed x) e1 e2) ⌊vs [//] xs⌋ = Let (BNamed x) e1 (e2⌊vs [//] xs⌋).
Proof.
  assert (∃ xs', xs = reverse xs') as [xs' ->].
  { exists (reverse xs). by rewrite reverse_involutive. }
  assert (∃ vs', vs = reverse vs') as [vs' ->].
  { exists (reverse vs). by rewrite reverse_involutive. }
  generalize dependent vs'. induction xs' as [|y xs]; first done.
  intros vs Hlen Hnin Hclosed. rewrite reverse_cons in Hnin.
  apply not_elem_of_app in Hnin as [Hnin Hneq].
  destruct vs as [|v vs].
  + rewrite length_reverse, length_cons in Hlen. simpl in Hlen; lia.
  + rewrite 2 reverse_cons, 2 length_app in Hlen. simpl in Hlen.
    rewrite 2 reverse_cons. do 2 (rewrite <- subst_vals_subst; last lia).
    rewrite IHxs; last done; last done; last lia.
    apply not_elem_of_cons in Hneq as [? _].
    simpl. case_decide; first congruence.
    specialize (is_closed_program _ Hclosed y v) as Hclosed'.
    simpl in Hclosed'. by rewrite Hclosed'.
Qed.
