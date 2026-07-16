import RUXt.Lang.Typechecker

namespace RUXt

/-! ### Libraries mapping function identifiers to their implementations -/

/-- Function implementations. -/
structure FunImpl where
  params : List (PVar × Ty)
  body : Expr
  ty : Ty
  safe : Bool
/-- The underlying, not-yet-validated map of implementations. -/
abbrev RawLibrary := PFun Fid FunImpl

/-- `e` is a well-typed program of type `τ` in context `𝕍`. -/
def SafeProgram (𝕍 : VarCtx) (Λ : RawLibrary) (e : Expr) (τ : Ty) : Prop :=
  match e with
  | .pure p => CheckPure 𝕍 p τ
  | .error => True
  | .assume t => CheckTerm 𝕍 t TyBool ∧ τ = TyUnit
  | .letIn bx e₁ e₂ => ∃ τ₁, SafeProgram 𝕍 Λ e₁ τ₁ ∧
      SafeProgram (match bx with | .named x => 𝕍.insert x τ₁ | .anon => 𝕍) Λ e₂ τ
  | .choice e₁ e₂ => SafeProgram 𝕍 Λ e₁ τ ∧ SafeProgram 𝕍 Λ e₂ τ
  | .alloc t => CheckTerm 𝕍 t TyInt ∧ τ = TyLoc
  | .free t => CheckTerm 𝕍 t TyLoc ∧ τ = TyUnit
  | .store t₁ t₂ => CheckTerm 𝕍 t₁ TyLoc ∧ (∃ τ', CheckTerm 𝕍 t₂ τ') ∧ τ = TyUnit
  | .load t => CheckTerm 𝕍 t TyLoc /- TODO: τ should match the value stored in t -/
  | .call f ts => ∃ γ : FunImpl, Λ f = γ ∧ γ.ty.compatible τ ∧
      CheckTerms 𝕍 ts (γ.params.map Prod.snd)

/-- Parameters of a function implementation are distinct. -/
def FunImpl.ParamsNodup (γ : FunImpl) : Prop := (γ.params.map Prod.fst).Nodup
/-- A function implementation is well-typed if its body is well-typed under the
context formed by its parameters. -/
def FunImpl.Typechecks (Λ : RawLibrary) (γ : FunImpl) : Prop :=
  SafeProgram (VarCtx.from (γ.params.map Prod.fst) (γ.params.map Prod.snd)) Λ γ.body γ.ty

/-- Libraries intrinsically contain only implementations with distinct parameter
names whose bodies typecheck under the contexts formed by those parameters. -/
structure Library where
  implementations : RawLibrary
  paramsNodup : ∀ f (γ : FunImpl), implementations f = γ → γ.ParamsNodup
  bodiesTypecheck : ∀ f (γ : FunImpl), implementations f = γ → γ.Typechecks implementations
instance : Coe Library RawLibrary := ⟨Library.implementations⟩

/-- Function `f` exists in library `Λ` with implementation `γ`. -/
def Library.MapsTo (Λ : Library) (f : Fid) (γ : FunImpl) : Prop :=
  Λ.implementations f = γ

/-- Parameters of every implementation obtained from a library are distinct. -/
theorem Library.params_nodup {Λ : Library} {f : Fid} {γ : FunImpl}
    (h : Λ.MapsTo f γ) : (γ.params.map Prod.fst).Nodup :=
  Λ.paramsNodup f γ h

/-- Every implementation obtained from a library has a well-typed body. -/
theorem Library.typechecks {Λ : Library} {f : Fid} {γ : FunImpl}
    (h : Λ.MapsTo f γ) :
    SafeProgram (VarCtx.from (γ.params.map Prod.fst) (γ.params.map Prod.snd))
      Λ.implementations γ.body γ.ty :=
  Λ.bodiesTypecheck f γ h

/-! ### Properties of safe programs -/

theorem safeProgram_subset {𝕍 𝕍' : VarCtx} {Λ : Library} {e : Expr} {τ : Ty}
    (hsafe : SafeProgram 𝕍' Λ e τ) (hsub : 𝕍' ⊆ 𝕍) :
    SafeProgram 𝕍 Λ e τ := by
  induction e generalizing 𝕍 𝕍' τ with
  | pure p => exact checkPure_subset hsafe hsub
  | error => trivial
  | assume t => exact ⟨checkTerm_subset hsafe.1 hsub, hsafe.2⟩
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, hsafe, hbx⟩ := hsafe
    refine ⟨τ₁, ih₁ hsafe hsub, ?_⟩
    cases bx with
    | anon => exact ih₂ hbx hsub
    | named x => exact ih₂ hbx (PFun.insert_mono _ _ hsub)
  | choice e₁ e₂ ih₁ ih₂ => exact ⟨ih₁ hsafe.1 hsub, ih₂ hsafe.2 hsub⟩
  | alloc t => exact ⟨checkTerm_subset hsafe.1 hsub, hsafe.2⟩
  | free t => exact ⟨checkTerm_subset hsafe.1 hsub, hsafe.2⟩
  | store t₁ t₂ =>
    obtain ⟨hcheck₁, ⟨τ, hcheck₂⟩, rfl⟩ := hsafe
    exact ⟨checkTerm_subset hcheck₁ hsub, ⟨τ, checkTerm_subset hcheck₂ hsub⟩, rfl⟩
  | load t => exact checkTerm_subset hsafe hsub
  | call f ts =>
    obtain ⟨γ, hγ, hcomp, hcheck⟩ := hsafe
    exact ⟨γ, hγ, hcomp, checkTerms_subset hcheck hsub⟩

theorem safeProgram_closed {𝕍 : VarCtx} {Λ : Library} {e : Expr} {τ : Ty}
    (hsafe : SafeProgram 𝕍 Λ e τ) : e.Closed 𝕍.dom := by
      induction e generalizing 𝕍 τ
      case error => trivial
      case pure => exact checkPure_closed hsafe
      case load => exact checkTerm_closed hsafe
      case assume => exact checkTerm_closed hsafe.1
      all_goals rcases hsafe with ⟨τ, hsafe⟩
      case letIn =>
        rename_i x _ _ ih₁ ih₂ _
        rcases x with (_ | x) <;> simp_all
        · exact ⟨ih₁ hsafe.1, ih₂ hsafe.2⟩
        · exact ⟨ih₁ hsafe.1, by simpa [PFun.dom_insert] using ih₂ hsafe.2⟩
      case choice => exact ⟨by solve_by_elim, by solve_by_elim⟩
      case alloc => exact checkTerm_closed τ
      case free => exact checkTerm_closed τ
      case store => exact ⟨checkTerm_closed τ, checkTerm_closed hsafe.1.choose_spec⟩
      case call => exact fun t ht => checkTerms_closed hsafe.2.2 t ht

/-- A main program is a safe program with no free variables. -/
def SafeMain : RawLibrary → Expr → Ty → Prop := SafeProgram ∅

theorem safeMain_pure {Λ : Library} {v : Val} :
    SafeMain Λ (.pure (.val v)) (v.ty) := by
  cases v <;> simp only [SafeMain, SafeProgram, CheckPure, CheckTerm,
    Val.ty, Val.baseTy, Ty.compatible]

theorem safe_call {Λ : Library} {f : Fid} {γ : FunImpl} (hmaps : Λ.MapsTo f γ) :
    SafeProgram (VarCtx.from (γ.params.map Prod.fst) (γ.params.map Prod.snd))
      Λ (.call f (Term.ofVars (γ.params.map Prod.fst))) γ.ty := by
  refine ⟨γ, hmaps, ?_, checkTerms_ofVars (by simp) (Λ.params_nodup hmaps)⟩
  cases γ.ty <;> simp [Ty.compatible]

theorem safeMain_closed {Λ : Library} {e : Expr} {τ : Ty}
    (hmain : SafeMain Λ e τ) : e.ClosedProgram :=
  safeProgram_closed hmain

end RUXt
