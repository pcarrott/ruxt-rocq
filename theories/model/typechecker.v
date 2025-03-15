From RUXt.lib Require Import gmap.
From RUXt.lang Require Export lang.


(* Identifiers for named types *)
Definition tid := string.
(* Base types *)
Definition val_tid (v : val) : tid :=
  match v with
  | VInt _ => "int"
  | VBool _ => "bool"
  | VLoc _ => "loc"
  | VUnit => "unit"
  end.

(* Function type signatures *)
Record fun_sign := mk_fun_sign { ty_in : list tid; ty_out : tid }.
Notation "{ τs ↣ₛ τ }" := (mk_fun_sign τs τ).
(* Signature contexts *)
Definition sign_ctx := gmap tid fun_sign.

(* Typed variable contexts *)
Definition var_ctx := gmap string tid.
Definition cons_var_ctx xs τs : var_ctx :=
  foldr (λ xτ, match xτ with (x, τ) => <[x := τ]> end) ∅ (zip xs τs).
(* Properties *)
Lemma insert_var_ctx xs τs x τ :
  length xs = length τs →
  <[x:=τ]> (cons_var_ctx xs τs) = cons_var_ctx (x :: xs) (τ :: τs).
Proof. done. Qed.
Lemma lookup_var_ctx_None xs τs x :
  length xs = length τs → x ∉ xs →
  cons_var_ctx xs τs !! x = None.
Proof.
  generalize dependent τs. induction xs as [|y xs].
  + intros τs Hlen _. by symmetry in Hlen; apply nil_length_inv in Hlen as ->.
  + intros [| τ τs] Hlen' Hnin; inversion Hlen' as [Hlen].
    apply not_elem_of_cons in Hnin as [Hneq Hnin].
    specialize (IHxs τs Hlen Hnin). unfold cons_var_ctx. simpl.
    by rewrite (lookup_insert_ne (cons_var_ctx xs τs)). 
Qed.
Lemma reverse_var_ctx xs τs :
  length xs = length τs → NoDup xs →
  cons_var_ctx xs τs = cons_var_ctx (reverse xs) (reverse τs).
Proof.
  intros Hlen Hdup. unfold cons_var_ctx.
  apply foldr_permutation.
  + by split; last congruence.
  + solve_proper.
  + intros i1 [x1 τ1] i2 [x2 τ2] 𝕍 Hneq.
    intros HSome1%lookup_zip_with_Some HSome2%lookup_zip_with_Some.
    destruct HSome1 as [?[? [Heq [Hx1 Hτ1]]]];
      symmetry in Heq; inversion Heq; subst; clear Heq.
    destruct HSome2 as [?[? [Heq [Hx2 Hτ2]]]];
      symmetry in Heq; inversion Heq; subst; clear Heq.
    assert (x1 ≠ x2) by by intros ->; eapply Hneq, NoDup_lookup.
    by apply insert_commute.
  + by apply zip_with_reverse.
Qed.

(* Well-typed terms are either values or well-typed variables *)
Definition check_term (𝕍 : var_ctx) t τ : bool :=
  match t with
  | TVar x => bool_decide (𝕍 !! x = Some τ)
  | TVal v => bool_decide (val_tid v = τ)
  end.
Fixpoint check_terms (𝕍 : var_ctx) ts τs : bool :=
  match ts, τs with
  | [], [] => true
  | t :: ts, τ :: τs => check_term 𝕍 t τ && check_terms 𝕍 ts τs
  | _, _ => false
  end.
(* Properties *)
Lemma check_terms_subseteq 𝕍 𝕍' ts τs :
  check_terms 𝕍' ts τs = true → 𝕍' ⊆ 𝕍 →
  check_terms 𝕍 ts τs = true.
Proof.
  generalize dependent τs. induction ts; first done.
  intros [| τ τs] Hcheck Hsub; first done.
  simpl in *. rewrite andb_true_iff in *.
  destruct Hcheck. split; last by apply IHts.
  unfold check_term in *. case_match; last done.
  case_decide; last done.
  eapply map_subseteq_spec in Hsub as ->; last done.
  by case_decide.
Qed.
Lemma check_terms_cons xs τs :
  length xs = length τs → NoDup xs →
  check_terms (cons_var_ctx xs τs) (TVars xs) τs = true.
Proof.
  generalize dependent τs. induction xs as [|x xs].
  + intros τs Hlen _. by symmetry in Hlen; apply nil_length_inv in Hlen as ->.
  + intros [| τ τs] Hlen' Hdup; inversion Hlen' as [Hlen].
    apply NoDup_cons in Hdup as [Hnin Hdup].
    specialize (IHxs τs Hlen Hdup).
    simpl. rewrite <- insert_var_ctx; last done.
    rewrite andb_true_iff. split.
    - rewrite (lookup_insert (cons_var_ctx xs τs)). by case_decide.
    - eapply check_terms_subseteq; first done.
      apply map_subseteq_spec. intros x' τ' HSome. 
      destruct (decide (x = x')) as [<-|Hneq].
      * by rewrite lookup_var_ctx_None in HSome.
      * by rewrite lookup_insert_Some; right.
Qed.
Lemma check_terms_dom 𝕍 ts τs x :
  check_terms 𝕍 ts τs = true → TVar x ∈ ts → x ∈ dom 𝕍.
Proof.
  generalize dependent τs. induction ts as [|t ts];
    intros τs Hcheck Hin; first inversion Hin.
  apply elem_of_cons in Hin. destruct Hin as [<-|Hin].
  + simpl in Hcheck. case_match; first done.
    apply andb_true_iff in Hcheck as [HSome _].
    by case_decide; first apply elem_of_dom.
  + destruct τs as [|τ τs]; first done.
    simpl in Hcheck. apply andb_true_iff in Hcheck as [_ Hcheck].
    by apply (IHts τs).
Qed.

(* A [safe] program only has calls to the library *)
Fixpoint safe_program 𝕍 (Δ : sign_ctx) e : option tid :=
  match e with
  | Let bx e1 e2 => 
      match safe_program 𝕍 Δ e1 with
      | Some τ =>
          match bx with
          | BNamed x => safe_program (<[x := τ]>𝕍) Δ e2
          | BAnon => safe_program 𝕍 Δ e2
          end
      | None => None
      end
  | Call f ts => 
      match Δ !! f with
      | Some { τs ↣ₛ τ } => if check_terms 𝕍 ts τs then Some τ else None
      | None => None
      end
  | _ => None
  end.
(* A [main] program is a safe program with no free variables *)
Definition safe_main := safe_program ∅.
(* Properties *)
Lemma safe_program_subseteq 𝕍 𝕍' Δ e τ :
  safe_program 𝕍' Δ e = Some τ → 𝕍' ⊆ 𝕍 →
  safe_program 𝕍 Δ e = Some τ.
Proof.
  generalize dependent τ. generalize dependent 𝕍'. generalize dependent 𝕍.
  induction e; try done; intros 𝕍 𝕍' τ Hmain Hsub.
  + unfold safe_main in Hmain; simpl in Hmain.
    case_match eqn:Hopt; last done.
    eapply IHe1 in Hopt; last done.
    case_match.
    - simpl. rewrite Hopt. by eapply IHe2.
    - simpl. rewrite Hopt. eapply IHe2; first done.
      by apply insert_mono.
  + simpl in *. case_match; last done. case_match.
    case_match eqn:Htrue; last done. case_match eqn:Hfalse; first done.
    exfalso. by eapply check_terms_subseteq in Hsub;
      first rewrite Hfalse in Hsub; last rewrite Htrue.
Qed.
Lemma safe_main_Some 𝕍 Δ e τ :
  safe_main Δ e = Some τ →
  safe_program 𝕍 Δ e = Some τ.
Proof.
  unfold safe_main. intros Hmain.
  eapply safe_program_subseteq; first done.
  apply map_empty_subseteq.
Qed.
Lemma safe_call Δ f xs τs τ :
  length xs = length τs → NoDup xs →
  Δ !! f = Some {τs ↣ₛ τ} →
  safe_program (cons_var_ctx xs τs) Δ (Call f (TVars xs)) = Some τ.
Proof.
  intros Hlen Hdup Htype. simpl. rewrite Htype.
  case_match eqn:Hfalse; first done.
  apply check_terms_cons in Hlen; last done.
  exfalso. by rewrite Hfalse in Hlen.
Qed.
Lemma safe_program_closed 𝕍 Δ e τ :
  safe_program 𝕍 Δ e = Some τ → closed_expr (dom 𝕍) e.
Proof.
  generalize dependent τ. generalize dependent 𝕍.
  induction e; try done; intros 𝕍 τ Hmain.
  + unfold safe_main in Hmain; simpl in Hmain.
    case_match eqn:Hopt; last done.
    specialize (IHe1 _ _ Hopt).
    case_match.
    - by specialize (IHe2 _ _ Hmain).
    - specialize (IHe2 _ _ Hmain).
      by rewrite (dom_insert_L 𝕍), union_comm_L in IHe2.
  + apply Forall_forall. intros [] Hin; last done.
    simpl in *. destruct (Δ !! f) as [[]|]; last done.
    case_match eqn:Htrue; last done.
    by eapply check_terms_dom.
Qed.
Lemma safe_main_closed Δ e τ :
  safe_main Δ e = Some τ → closed_program e.
Proof.
  intros Hmain%safe_program_closed.
  by replace (dom (∅ : var_ctx)) with (∅ : gset string) in Hmain.
Qed.
