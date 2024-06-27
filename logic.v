From RUXt Require Import typing.


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
| A_Star (a1 a2 : asrt)
| A_Interp (𝕋 : list typing).
(* Assertion satisfiability *)
Fixpoint eval_asrt (h : heap) (a : asrt) : Prop :=
  match a with
  | A_PureEq p1 p2 => eval_pure p1 = eval_pure p2
  | A_PureTrue p => eval_pure p = Ok (VBool true)
  | A_Emp => h = ∅
  | A_Points p1 p2 => ∃ l v, eval_pure p1 = Ok (VLoc l) ∧ eval_pure p2 = Ok v ∧ h = {[l := LangVal v]}
  | A_Freed p => ∃ l, eval_pure p = Ok (VLoc l) ∧ h = {[l := Freed]}
  | A_Uninit p => ∃ l, eval_pure p = Ok (VLoc l) ∧ h = {[l := Poison]}
  | A_False => False
  | A_Implies a1 a2 => eval_asrt h a1 → eval_asrt h a2
  | A_Star a1 a2 => ∃ h1 h2, h = h1 ∪ h2 ∧ h1 ##ₘ h2 ∧ eval_asrt h1 a1 ∧ eval_asrt h2 a2
  | A_Interp 𝕋 => Forall interpret 𝕋
  end.
Definition assert (a : asrt) : Prop := ∀ h, eval_asrt h a.

(* Function specifications *)
Inductive fun_spec := FunSpec (vs : list val) (P Q : asrt) (ε : exit).
Notation "[ ( vs ) P | ε . Q ]" := (FunSpec vs P Q ε).
Definition spec_ctx : Set := gmap string fun_spec.

(* Under-approximate triples - UX specifications *)
Definition ux_spec (γ : impl_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  ∀ h', eval_asrt h' Q → ∃ h, eval_asrt h P ∧ (γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩).
Definition valid_specs (γ : impl_ctx) (Γ : spec_ctx) : Prop :=
  ∀ f vs P Q ε, Γ !! f = Some [(vs) P | ε. Q] →
  ∃ xs e, γ !! f = Some {(xs) e} ∧ ux_spec γ e P Q ε.
Definition ux_triple (Γ : spec_ctx) (e : expr) (P Q : asrt) (ε : exit) : Prop :=
  ∀ γ, valid_specs γ Γ → ux_spec γ e P Q ε.
Notation "Γ ⊢ ⌈ P ⌉ e ⌈ ε . Q ⌉" := (ux_triple Γ e P Q ε)
  (at level 100, no associativity).

(* Over-approximate triples - Typing judgements *)
Definition ox_spec (γ : impl_ctx) (e : expr) (P Q : asrt) (v : val) : Prop :=
  ∀ h, eval_asrt h P → ∀ h' ε, (γ ⊢ ⟨ h | e ⟩ ⇓ ⟨ h' | ε ⟩) → eval_asrt h' Q ∧ ε = Ok v.
Definition valid_types (γ : impl_ctx) (Δ : type_ctx) : Prop :=
  ∀ f τs τ, Δ !! f = Some {τs ↣ τ} →
  ∃ xs e, γ !! f = Some {(xs) e} ∧
  ∀ vs, ∃ e', subst_l xs vs e = Some e' →
  ∃ ts, typings vs (TOwn <$> τs) = Some ts ∧
  ∃ v, ox_spec γ e' (A_Interp ts) (A_Interp [v ⊲ TOwn τ]) v.
Definition ox_triple (Δ : type_ctx) (e : expr) (𝕋 𝕌 : list typing) (v : val) : Prop :=
  ∀ γ, valid_types γ Δ → ox_spec γ e (A_Interp 𝕋) (A_Interp 𝕌) v.
Notation "Δ | 𝕋 ⊢ e ⊣ v . 𝕌" := (ox_triple Δ e 𝕋 𝕌 v)
  (at level 100, no associativity).
