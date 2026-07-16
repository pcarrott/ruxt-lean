import RUXt.Lib.PFun
import RUXt.Lang.Types
import RUXt.Lang.Lang

namespace RUXt

/-! ### Contexts mapping program variables to their types -/

/-- The type of variable contexts. -/
abbrev VarCtx := PFun PVar Ty

/-- Build a variable context from parallel lists of names and types. -/
def VarCtx.from (xs : List PVar) (τs : List Ty) : VarCtx :=
  (xs.zip τs).foldr (fun (x, τ) 𝕍 => 𝕍.insert x τ) ∅

private theorem VarCtx.from_insert {xs : List PVar} {τs : List Ty} (x : PVar) (τ : Ty) :
    (VarCtx.from xs τs).insert x τ = VarCtx.from (x :: xs) (τ :: τs) := rfl

private theorem VarCtx.from_lookup_none {xs : List PVar} {τs : List Ty} {x : PVar}
    (hnin : x ∉ xs) : VarCtx.from xs τs x = Part.none := by
  induction xs generalizing τs with
  | nil => rfl
  | cons y ys ih =>
    cases τs with
    | nil => simp [VarCtx.from]
    | cons τ τs =>
      simp only [List.mem_cons, not_or] at hnin
      rw [← VarCtx.from_insert y τ, PFun.insert_apply_ne _ _ hnin.1]
      exact ih hnin.2

/-! ### Typechecking pure expressions -/

/-- The base type of a value. -/
def Val.baseTy : Val → BaseTy
  | .int _ => .int
  | .bool _ => .bool
  | .loc _ => .loc
  | .unit => .unit
/-- The type of a value. -/
def Val.ty : Val → Ty
  | v => .base v.baseTy

/-- Typechecker for terms. -/
def CheckTerm (𝕍 : VarCtx) (t : Term) (τ : Ty) : Prop :=
  match t with
  | .var x => ∃ τₓ : Ty, 𝕍 x = τₓ ∧ τₓ.compatible τ
  | .val v => (Ty.base v.baseTy).compatible τ
/-- Typechecker for lists of terms. -/
def CheckTerms (𝕍 : VarCtx) : List Term → List Ty → Prop
  | [], [] => True
  | t :: ts, τ :: τs => CheckTerm 𝕍 t τ ∧ CheckTerms 𝕍 ts τs
  | _, _ => False
/-- Typechecker for pure expressions. -/
def CheckPure (𝕍 : VarCtx) : Pure → Ty → Prop
  | .term t, τ =>
      CheckTerm 𝕍 t τ
  | .unOp .minus p, τ =>
      CheckPure 𝕍 p TyInt ∧ TyInt.compatible τ
  | .unOp .not p, τ =>
      CheckPure 𝕍 p TyBool ∧ τ = TyBool
  | .binOp .add p₁ p₂, τ | .binOp .mod p₁ p₂, τ =>
      CheckPure 𝕍 p₁ TyInt ∧ CheckPure 𝕍 p₂ TyInt ∧ TyInt.compatible τ
  | .binOp .eq p₁ p₂, τ | .binOp .lt p₁ p₂, τ =>
      CheckPure 𝕍 p₁ TyInt ∧ CheckPure 𝕍 p₂ TyInt ∧ τ = TyBool
  | .binOp .offset p₁ p₂, τ =>
      CheckPure 𝕍 p₁ TyLoc ∧ CheckPure 𝕍 p₂ TyInt ∧ τ = TyLoc

/-! ### Monotonicity -/

theorem checkTerm_subset {𝕍 𝕍' : VarCtx} {t : Term} {τ : Ty}
    (hcheck : CheckTerm 𝕍' t τ) (hsub : 𝕍' ⊆ 𝕍) : CheckTerm 𝕍 t τ := by
  cases t with
  | val v => exact hcheck
  | var x =>
    obtain ⟨τ', hx, hc⟩ := hcheck
    exact ⟨τ', PFun.subset_apply hsub hx, hc⟩

theorem checkTerms_subset {𝕍 𝕍' : VarCtx} {ts : List Term} {τs : List Ty}
    (hcheck : CheckTerms 𝕍' ts τs) (hsub : 𝕍' ⊆ 𝕍) : CheckTerms 𝕍 ts τs := by
  induction ts generalizing τs with
  | nil => cases τs <;> simp_all [CheckTerms]
  | cons t ts ih =>
    cases τs with
    | nil => exact hcheck.elim
    | cons τ τs => exact ⟨checkTerm_subset hcheck.1 hsub, ih hcheck.2⟩

theorem checkPure_subset {𝕍 𝕍' : VarCtx} {p : Pure} {τ : Ty}
    (hcheck : CheckPure 𝕍' p τ) (hsub : 𝕍' ⊆ 𝕍) : CheckPure 𝕍 p τ := by
  induction p generalizing τ with
  | term t => exact checkTerm_subset hcheck hsub
  | unOp op p ih => cases op <;> exact ⟨ih hcheck.1, hcheck.2⟩
  | binOp op p₁ p₂ ih₁ ih₂ => cases op <;> exact ⟨ih₁ hcheck.1, ih₂ hcheck.2.1, hcheck.2.2⟩

/-! ### Closed pure expressions -/

theorem checkTerm_closed {𝕍 : VarCtx} {t : Term} {τ : Ty}
    (h : CheckTerm 𝕍 t τ) : t.Closed 𝕍.dom := by
  cases t with
  | val v => trivial
  | var x =>
    obtain ⟨τ', hx, _⟩ := h
    exact PFun.mem_dom.mpr ⟨τ', hx⟩

theorem checkTerms_closed {𝕍 : VarCtx} {ts : List Term} {τs : List Ty}
    (h : CheckTerms 𝕍 ts τs) : ∀ t ∈ ts, t.Closed 𝕍.dom := by
  induction ts generalizing τs with
  | nil => simp
  | cons head tail ih =>
    cases τs with
    | nil => exact h.elim
    | cons τ τs =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact checkTerm_closed h.1
      · exact ih h.2 t ht

theorem checkPure_closed {𝕍 : VarCtx} {p : Pure} {τ : Ty}
    (h : CheckPure 𝕍 p τ) : p.Closed 𝕍.dom := by
  induction p generalizing τ with
  | term t => exact checkTerm_closed h
  | unOp op p ih => cases op <;> exact ih h.1
  | binOp op p₁ p₂ ih₁ ih₂ => cases op <;> exact ⟨ih₁ h.1, ih₂ h.2.1⟩

/-! ### Typechecked variables -/

theorem checkTerms_ofVars {xs : List PVar} {τs : List Ty}
    (hlen : xs.length = τs.length) (hdup : xs.Nodup) :
    CheckTerms (VarCtx.from xs τs) (Term.ofVars xs) τs := by
  induction xs generalizing τs with
  | nil => cases τs <;> simp_all [CheckTerms, Term.ofVars]
  | cons x xs ih =>
    cases τs with
    | nil => simp at hlen
    | cons τ τs =>
      obtain ⟨hnin, hdup'⟩ := List.nodup_cons.mp hdup
      rw [← VarCtx.from_insert x τ]
      refine ⟨?_, ?_⟩
      · exact ⟨τ, by simp [PFun.insert_apply], by cases τ <;> simp [Ty.compatible]⟩
      · simp at hlen
        refine checkTerms_subset (ih hlen hdup') ?_
        intro a b hab
        by_cases hax : a = x
        · subst hax
          rw [VarCtx.from_lookup_none hnin] at hab
          exact absurd hab (by simp)
        · rwa [PFun.insert_apply_ne _ _ hax]

/-! ### Variable context extension with reversed insertion order -/

/-- Extends an existing variable context with the provided bindings. -/
def VarCtx.extend (𝕍 : VarCtx) (xs : List PVar) (τs : List Ty) : VarCtx :=
  (xs.zip τs).foldl (fun 𝕍 (x, τ) => 𝕍.insert x τ) 𝕍

theorem VarCtx.extend_empty {xs : List PVar} {τs : List Ty} (hdup : xs.Nodup) :
    VarCtx.extend ∅ xs τs = VarCtx.from xs τs := by
  have h_VarCtx.from {xs : List PVar} {τs : List Ty} : xs.Nodup →
      ∀ (𝕍 : VarCtx),
        List.foldl (fun 𝕍 (x, τ) => PFun.insert x τ 𝕍) 𝕍 (xs.zip τs) = (VarCtx.from xs τs) ∪ 𝕍 := by
    revert τs
    induction xs with
    | nil => intro τs _ m; simp [VarCtx.from, PFun.empty_union]
    | cons x xs ih =>
      intro τs hdup m
      rcases τs with _ | ⟨τ, τs⟩
      · simp [VarCtx.from]
      · obtain ⟨hnin, hdup'⟩ := List.nodup_cons.mp hdup
        rw [List.zip_cons_cons, List.foldl_cons, ← VarCtx.from_insert x τ,
          PFun.insert_union_l, ih hdup' (PFun.insert x τ m)]
        ext y
        by_cases hy : y = x
        · subst hy
          simp [PFun.union_apply, PFun.insert_apply,
            VarCtx.from_lookup_none hnin, Part.not_none_dom]
        · simp [PFun.union_apply, PFun.insert_apply, hy]
  rw [VarCtx.extend, h_VarCtx.from hdup ∅, PFun.union_empty]

theorem VarCtx.extend_nil {𝕍 : VarCtx} : 𝕍.extend [] [] = 𝕍 := rfl

theorem VarCtx.extend_cons {𝕍 : VarCtx} {xs : List PVar} {τs : List Ty} {x : PVar} {τ : Ty} :
    𝕍.extend (x :: xs) (τ :: τs) = VarCtx.extend (𝕍.insert x τ) xs τs := rfl

end RUXt
