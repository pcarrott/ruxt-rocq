From RUXt.lang Require Import semantics.
From RUXt.types Require Export type.
From RUXt.types.lib Require Export int bool own unit.
From RUXt.model Require Export logic.


(*** The Type Refutation Algorithm ***)

(* Libraries *)
Record library := mk_library { impls : impl_ctx; types : type_ctx }.
(* Well-typed states that can be derived by some UX logic *)
Definition derivable_post Λ is_src e τ Q ε :=
  (* Some function f outputs values of type τ *)
  ∃ f τs, types Λ !! f = Some {τs ↣ τ} ∧
  (* Program s generates values vs and precondition [P] *)
  ∃ s vs P, is_src s τs vs P ∧ e = Let <> s (Call f (TVals vs)) ∧
  (* [ε:Q] is a postcondition obtained from executing f *)
  ∃ L, (derivable_spec L) (impls Λ) (Call f (TVals vs)) P Q ε.

(* Summaries for type spaces *)
Record summary := mk_summary { ty : type; ret : val; post : asrt; src : expr }.
Definition summ_ctx := list summary.
(* Well-formed input values and preconditions *)
Notation skip := (Pure (PVal VUnit)).
Inductive wf_witness : summ_ctx → expr → list typing → asrt → Prop :=
| I_Emp Σ :
  wf_witness Σ skip [] EMP
| I_Star Σ e 𝕋 P τ v Q s :
  wf_witness Σ e 𝕋 P → mk_summary τ v Q s ∈ Σ →
  wf_witness Σ (Let <> s e) (v ⊲ τ :: 𝕋) (Q ∗ P).
Definition wf_src Σ e τs vs P := wf_witness Σ e (vs [⊲] τs) P ∧ length vs = length τs.

(* Type refutation algorithm *)
Definition try_refute Λ Σ (ς : summary + expr) :=
  (* Postcondition [ε: Q] is reachable with output type τ *)
  ∃ e τ Q ε, derivable_post Λ (wf_src Σ) e τ Q ε ∧ sat Q ∧
  (* A new summary for τ is learned iff termination is successful *)
  ς = match ε with Ok v => inl (mk_summary τ v Q e) | _ => inr e end.
(* Well-formed type summary contexts *)
Inductive wf_summ_ctx : library → summ_ctx → Prop :=
| R_Nil Λ : 
  wf_summ_ctx Λ []
| R_Cons Λ Σ ς :
  wf_summ_ctx Λ Σ → try_refute Λ Σ (inl ς) →
  wf_summ_ctx Λ (ς :: Σ).

(* Semantic interpretation of valid inputs *)
Notation witness_program Σ := (foldr (λ ς e, Let <> (src ς) e) skip Σ).
Definition valid_witness Σ e 𝕋 P :=
  ∃ Σ', Σ' ⊆ Σ ∧
    e = witness_program Σ' ∧
    𝕋 = map ret Σ' [⊲] map ty Σ' ∧
    P = [∗ map post Σ', id].
(* Soundness *)
Theorem input_soundness Σ e 𝕋 P :
  wf_witness Σ e 𝕋 P → valid_witness Σ e 𝕋 P.
Proof.
  intros Hinput. induction Hinput.
  + exists []. by split; first apply list_subseteq_nil.
  + destruct IHHinput as [Σ' [Hsub [-> [-> ->]]]].
    set (ς := {| ty := τ; ret := v; post := Q ; src := s|}).
    exists (ς :: Σ'). split; last done. by apply list_subseteq_cons_iff.
Qed.

From RUXt.lib Require Import gmap.
(* A program constructed solely from [safe] calls to the library *)
Fixpoint well_typed_call (𝕋 : gmap string type) ts τs τ :=
  match ts, τs with
  | [], [] => Some τ
  | t :: ts, τ :: τs =>
      match t with
      | TVar x => 
          match 𝕋 !! x with
          | Some τ' => if (decide (ty_name τ = ty_name τ'))
                       then well_typed_call 𝕋 ts τs τ else None
          | None => None
          end
      | TVal v =>
          match v with
          | VInt _ => if (decide (ty_name τ = "int"))
                      then well_typed_call 𝕋 ts τs τ else None
          | VBool _ => if (decide (ty_name τ = "bool"))
                       then well_typed_call 𝕋 ts τs τ else None
          | VLoc _ => if (decide (ty_name τ = "loc"))
                      then well_typed_call 𝕋 ts τs τ else None
          | VUnit => if (decide (ty_name τ = ""))
                     then well_typed_call 𝕋 ts τs τ else None
          end
      end
  | _, _ => None
  end.
(* A [main] program starts from [EMP] and only has [safe] calls to the library *)
Fixpoint safe_program 𝕋 (Δ : type_ctx) e : option type :=
  match e with
  | Let bx e1 e2 => 
      match safe_program 𝕋 Δ e1 with
      | Some τ =>
          match bx with
          | BNamed x => safe_program (<[x := τ]>𝕋) Δ e2
          | BAnon => safe_program 𝕋 Δ e2
          end
      | None => None
      end
  | Call f ts => 
      match Δ !! f with
      | Some {τs ↣ τ} => well_typed_call 𝕋 ts τs τ
      | None => None
      end
  | Pure PUnit => Some unit
  | _ => None
  end.
Definition safe_main := safe_program ∅.

(* A [main] function starts from [EMP] and only has [safe] calls to the library *)
Definition reachable_from_main Λ e (Q : asrt) (ε : exit) :=
  ux_frame_triple (impls Λ) e EMP Q ε ∧ ∃ τ, safe_main (types Λ) e = Some τ.

(* Semantic interpretation of valid summaries *)
Definition valid_summ_ctx Λ (Σ : summ_ctx) :=
  ∀ ς, ς ∈ Σ → reachable_from_main Λ (src ς) (post ς) (Ok (ret ς)).
(* Properties *)
Lemma subseteq_reachable Λ Σ Σ' :
  valid_summ_ctx Λ Σ → Σ' ⊆ Σ →
  ∃ v, reachable_from_main Λ (witness_program Σ') ([∗ map post Σ', id]) (Ok v).
Proof.
  intros Hsumm Hsub. induction Σ'.
  + simpl. exists VUnit.
    by split; first apply pure_spec; last eexists.
  + simpl. unfold valid_summ_ctx in Hsumm.
    eapply list_subseteq_cons_iff in Hsub as [Hin Hsub].
    apply Hsumm in Hin as [Htriple [τ Hsafe]].
    apply IHΣ' in Hsub as [v [Htriple' [τ' Hsafe']]].
    exists v. split.
    - by eapply let_spec; last eapply frame_spec.
    - unfold safe_main, safe_program in *.
      exists τ'. by rewrite Hsafe, Hsafe'.
Qed.
Lemma derivable_for_main Λ Σ e τ Q ε :
  valid_summ_ctx Λ Σ → derivable_post Λ (wf_src Σ) e τ Q ε →
  reachable_from_main Λ e Q ε.
Proof.
  intros Hsumm [f [τs [Htype [s [vs [P [[Hinput Hlen] [-> [L Hspec%ux_frame_soundness]]]]]]]]].
  apply input_soundness in Hinput as [Σ'' [Hsub' [-> [H𝕋 ->]]]].
  specialize (subseteq_reachable _ _ _ Hsumm Hsub') as [? Hreach].
  destruct Hreach as [Htriple [τ' Hsafe]].
  split.
  + by eapply let_spec.
  + unfold safe_main, safe_program in *.
    exists τ. rewrite Hsafe, Htype.
    admit.
Admitted.
(* Soundness *)
Theorem summ_ctx_soundness Λ Σ :
  wf_summ_ctx Λ Σ → valid_summ_ctx Λ Σ.
Proof.
  intros Hsumm. induction Hsumm.
  + inversion 1.
  + intros ς' Hin. apply elem_of_cons in Hin as [<-|Hin].
    - destruct H as [e [τ [Q [ε [Hpost [Hsat Hε]]]]]].
      destruct ε; try done. inversion Hε; subst; clear Hε.
      by eapply derivable_for_main in IHHsumm as Hreach.
    - by apply IHHsumm in Hin as Hreach.
Qed.

(* A type assignment in the library can be refuted *)
Definition has_refuted_type Λ e :=
  ∃ Σ, wf_summ_ctx Λ Σ ∧ try_refute Λ Σ (inr e).
(* A [main] program exhibits undefined behaviour *)
Definition inadequate Λ e :=
  ∃ h, (impls Λ) ⊢ ⟨ ∅ | e ⟩ ⇓ ⟨ h | Err ⟩ ∧ ∃ τ, safe_main (types Λ) e = Some τ.
(* Adequacy result for refuted type assignments *)
Theorem inadequacy Λ e :
  has_refuted_type Λ e → inadequate Λ e.
Proof.
  intros [Σ [Hctx%summ_ctx_soundness [s [τ [Q [ε [Hpost [Hsat Hε]]]]]]]].
  eapply derivable_for_main in Hpost as [Hux%ux_triple_preservation []]; last done.
  destruct Hsat as [?[?[->]]%Hux].
  destruct ε; inversion Hε; subst.
  all: by eexists; split; last by eexists.
Qed.
