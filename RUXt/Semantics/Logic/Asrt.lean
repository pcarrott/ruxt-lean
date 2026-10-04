import RUXt.Model.Logic

/-!
# Semantics of assertions

Building symbolic expressions and reading them at a tuple of symbolic values; the meaning of
assertions — which heaps satisfy an assertion (`HProp`), satisfiability (`Sat`), validity and
entailment (`⊨`) and logical equivalence (`⊣⊢`) — together with the typing judgement the opaque
predicate is stated with (`SafeProgram`); and the basic separation-logic properties of the
connectives.
-/

namespace RUXt

open scoped PFun

universe u v w

/-! ## Building symbolic expressions

Every way of building an expression lifts pointwise to symbolic expressions; the arguments of
each builder are themselves read off the telescope at the symbolic values the expression is
taken at. -/

/-- An expression may be written where a lifted one is expected. -/
instance : CoeTail Expr LExpr.{u} := ⟨ULift.up⟩

namespace SymExpr

variable {tt tt' : Tele.{u + 1}}

/-- The symbolic expression running `e` whatever the symbolic values. -/
def const (e : Expr) : SymExpr tt := teleLift fun _ => e

/-- Symbolic substitution of a symbolic value for a binder (`Expr.subst` pointwise). -/
def subst (e : SymExpr tt) (x : Binder) (v : TeleLift tt Val) : SymExpr tt :=
  teleLift fun args => (e.at args).subst x (v.at args)

/-- Symbolic substitution of a symbolic list of values for a list of variables (`Expr.substs`
pointwise). -/
def substs (body : SymExpr tt) (xs : List PVar) (vals : TeleLift tt (List Val)) : SymExpr tt :=
  teleLift fun args => (body.at args).substs xs (Term.ofVals (vals.at args))

/-- Symbolic sequencing (`Expr.letIn` pointwise). -/
def letIn (x : Binder) (e₁ e₂ : SymExpr tt) : SymExpr tt :=
  teleLift fun args => .letIn x (e₁.at args) (e₂.at args)

/-- Symbolic nondeterministic choice (`Expr.choice` pointwise). -/
def choice (e₁ e₂ : SymExpr tt) : SymExpr tt :=
  teleLift fun args => .choice (e₁.at args) (e₂.at args)

/-- The symbolic call of `f` at symbolic type arguments and symbolic argument values
(`Expr.call` pointwise). -/
def call (f : Fid) (tys : TeleLift tt (List Ty)) (vals : TeleLift tt (List Val)) :
    SymExpr tt :=
  teleLift fun args => .call f (tys.at args) (Term.ofVals (vals.at args))

/-- The symbolic body of the declaration `φ`, concretised at symbolic type arguments and run at
symbolic argument values, both well-sized. -/
def body (φ : FunDecl) (tys : TeleLift tt φ.TyArgs) (vals : TeleLift tt φ.ValArgs) :
    SymExpr tt :=
  teleLift fun args => (φ.concretise (tys.at args)).with (vals.at args)

/-- A symbolic expression over `tt` read over `tt'` along a map of symbolic values. -/
def reindex (e : SymExpr tt) (f : TeleArg tt' → TeleArg tt) : SymExpr tt' :=
  teleLift fun args => e.at (f args)

/-! ## Reading a symbolic expression at a tuple of symbolic values -/

@[simp] theorem const_at (e : Expr) (args : TeleArg tt) :
    (const (tt := tt) e).at args = e := teleLift_at ..

@[simp] theorem subst_at (e : SymExpr tt) (x : Binder) (v : TeleLift tt Val)
    (args : TeleArg tt) : (e.subst x v).at args = (e.at args).subst x (v.at args) :=
  teleLift_at ..

@[simp] theorem substs_at (body : SymExpr tt) (xs : List PVar) (vals : TeleLift tt (List Val))
    (args : TeleArg tt) :
    (body.substs xs vals).at args = (body.at args).substs xs (Term.ofVals (vals.at args)) :=
  teleLift_at ..

@[simp] theorem letIn_at (x : Binder) (e₁ e₂ : SymExpr tt) (args : TeleArg tt) :
    (letIn x e₁ e₂).at args = .letIn x (e₁.at args) (e₂.at args) := teleLift_at ..

@[simp] theorem choice_at (e₁ e₂ : SymExpr tt) (args : TeleArg tt) :
    (choice e₁ e₂).at args = .choice (e₁.at args) (e₂.at args) := teleLift_at ..

@[simp] theorem call_at (f : Fid) (tys : TeleLift tt (List Ty)) (vals : TeleLift tt (List Val))
    (args : TeleArg tt) :
    (call f tys vals).at args = .call f (tys.at args) (Term.ofVals (vals.at args)) :=
  teleLift_at ..

@[simp] theorem body_at (φ : FunDecl) (tys : TeleLift tt φ.TyArgs) (vals : TeleLift tt φ.ValArgs)
    (args : TeleArg tt) :
    (body φ tys vals).at args = (φ.concretise (tys.at args)).with (vals.at args) := teleLift_at ..

@[simp] theorem reindex_at (e : SymExpr tt) (f : TeleArg tt' → TeleArg tt)
    (args : TeleArg tt') : (e.reindex f).at args = e.at (f args) := teleLift_at ..

end SymExpr

/-! ## Semantics of assertions -/

/-- `e` is a well-typed program of type `τ` in context `𝕍`. -/
def SafeProgram (𝕍 : VarCtx) (Λ : Library) (τ : Ty) : Expr → Prop
  | .pure p => CheckPure 𝕍 p τ
  | .assume t => CheckTerm 𝕍 t .bool ∧ τ = .unit
  | .letIn bx e₁ e₂ => ∃ τ₁, SafeProgram 𝕍 Λ τ₁ e₁ ∧
      SafeProgram (match bx with | .named x => 𝕍.insert x τ₁ | .anon => 𝕍) Λ τ e₂
  | .choice e₁ e₂ => SafeProgram 𝕍 Λ τ e₁ ∧ SafeProgram 𝕍 Λ τ e₂
  | .call f τs ts => ∃ γ : FunImpl, Λ.Instantiates f τs γ ∧ γ.ty = τ ∧ γ.safe ∧
      CheckTerms 𝕍 ts (γ.params.map Prod.snd)
  | _ => false
/-- A main program is a safe program with no free variables. -/
def SafeMain : Library → Ty → Expr → Prop := SafeProgram ∅

/-- Satisfaction of an assertion by a heap. -/
def HProp (h : Heap) : Asrt → Prop
  | .pure P => h = ∅ ∧ P
  | .true => True
  | .false => False
  | .and a₁ a₂ => HProp h a₁ ∧ HProp h a₂
  | .or a₁ a₂ => HProp h a₁ ∨ HProp h a₂
  | .implies a₁ a₂ => HProp h a₁ → HProp h a₂
  | .ex P => ∃ x, HProp h (P x)
  | .emp => h = ∅
  | .single ⟨b, i⟩ bv => h = PFun.singleton b bv ∧ i = 0
  | .star a₁ a₂ => ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ HProp h₁ a₁ ∧ HProp h₂ a₂
  | .opaque Λ τ v => ∃ e, Λ ⊢ ⟨ ∅ | e ⟩ ⇓ᵢ ⟨ h | .ok v ⟩ ∧ SafeMain Λ τ e

/-- `P ⊨ Q`: every heap satisfying `P` has a subheap satisfying `Q`. -/
def HModels (P Q : Asrt) : Prop :=
  ∀ h, HProp h P → ∃ h', h' ⊆ h ∧ HProp h' Q
@[inherit_doc] scoped infix:24 " ⊨ " => HModels
/-- `⊨ P`: `P` holds of every heap. -/
def HValid (P : Asrt) : Prop := ∀ h, HProp h P
@[inherit_doc] scoped prefix:24 "⊨ " => HValid
/-- `P ⊣⊢ Q`: `P` and `Q` are satisfied by exactly the same heaps. -/
def HEquiv (P Q : Asrt) : Prop := ∀ h, HProp h P ↔ HProp h Q
@[inherit_doc] scoped infix:24 " ⊣⊢ " => HEquiv
/-- `Sat`: satisfiability. -/
def Sat (P : Asrt) : Prop := ∃ h, HProp h P

/-- An assertion lifted into a higher universe: the type bound by an existential is replaced by
its `ULift`. -/
def Asrt.ulift : Asrt.{v} → Asrt.{max v w}
  | .pure P => .pure P
  | .true => .true
  | .false => .false
  | .and a₁ a₂ => .and (Asrt.ulift a₁) (Asrt.ulift a₂)
  | .or a₁ a₂ => .or (Asrt.ulift a₁) (Asrt.ulift a₂)
  | .implies a₁ a₂ => .implies (Asrt.ulift a₁) (Asrt.ulift a₂)
  | .ex (X := X) P => .ex fun x : ULift.{w, v} X => Asrt.ulift (P x.down)
  | .emp => .emp
  | .single l bv => .single l bv
  | .star a₁ a₂ => .star (Asrt.ulift a₁) (Asrt.ulift a₂)
  | .opaque Λ τ x => .opaque Λ τ x

/-! ## Properties of assertions -/

@[simp] theorem Asrt.iter_nil {X : Type _} (P : X → Asrt) :
    Asrt.iter ([] : List X) P = .emp := rfl
@[simp] theorem Asrt.iter_cons {X : Type _} (P : X → Asrt) (x : X) (xs : List X) :
    Asrt.iter (x :: xs) P = P x ∗ Asrt.iter xs P := rfl
@[simp] theorem Asrt.iterI_map {X : Type _} {Y : Type _} (g : X → Y) (P : ℕ → Y → Asrt) :
    ∀ (xs : List X), Asrt.iterI (xs.map g) P = Asrt.iterI xs (fun n x => P n (g x))
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, Asrt.iterI]
    rw [Asrt.iterI_map g (fun n => P (n + 1)) xs]
@[simp] theorem Asrt.iter_map {X : Type _} {Y : Type _} (g : X → Y) (P : Y → Asrt)
    (xs : List X) : Asrt.iter (xs.map g) P = Asrt.iter xs (fun x => P (g x)) :=
  Asrt.iterI_map g (fun _ => P) xs

section hProp_simp

variable {h : Heap}

@[simp] theorem hProp_pure {P : Prop} : HProp h ⌞P⌟ ↔ h = ∅ ∧ P := Iff.rfl
@[simp] theorem hProp_true : HProp h .true ↔ True := Iff.rfl
@[simp] theorem hProp_false : HProp h .false ↔ False := Iff.rfl
@[simp] theorem hProp_and {a₁ a₂ : Asrt} :
    HProp h (a₁ ∧ₕ a₂) ↔ HProp h a₁ ∧ HProp h a₂ := Iff.rfl
@[simp] theorem hProp_or {a₁ a₂ : Asrt} :
    HProp h (a₁ ∨ₕ a₂) ↔ HProp h a₁ ∨ HProp h a₂ := Iff.rfl
@[simp] theorem hProp_implies {a₁ a₂ : Asrt} :
    HProp h (a₁ →ₕ a₂) ↔ (HProp h a₁ → HProp h a₂) := Iff.rfl
@[simp] theorem hProp_ex {X : Type _} {P : X → Asrt} :
    HProp h (.ex P) ↔ ∃ x, HProp h (P x) := Iff.rfl
@[simp] theorem hProp_emp : HProp h .emp ↔ h = ∅ := Iff.rfl
@[simp] theorem hProp_single {l : Loc} {bv : BlockValue} :
    HProp h (.single l bv) ↔ h = PFun.singleton l.1 bv ∧ l.2 = 0 := Iff.rfl
@[simp] theorem hProp_star {a₁ a₂ : Asrt} :
    HProp h (a₁ ∗ a₂) ↔
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ HProp h₁ a₁ ∧ HProp h₂ a₂ := Iff.rfl
@[simp] theorem hProp_pointsTo {l : Loc} {v : Val} :
    HProp h (l ↦ v) ↔
    h = PFun.singleton l.1 (.block 1 (PFun.singleton l.2 (.val v))) ∧ l.2 = 0 := Iff.rfl
@[simp] theorem hProp_pointsToFreed {l : Loc} :
    HProp h (l ↦∅) ↔ h = PFun.singleton l.1 .freed ∧ l.2 = 0 := Iff.rfl
@[simp] theorem hProp_pointsToUninit {l : Loc} :
    HProp h (l ↦?) ↔
    h = PFun.singleton l.1 (.block 1 (PFun.singleton l.2 .poison)) ∧ l.2 = 0 := Iff.rfl

end hProp_simp

/-- Lifting an assertion does not change the heaps that satisfy it. -/
@[simp] theorem hProp_ulift {h : Heap} {a : Asrt.{v}} :
    HProp h (Asrt.ulift.{v, w} a) ↔ HProp h a := by
  induction a generalizing h with
  | pure P => exact Iff.rfl
  | «true» => exact Iff.rfl
  | «false» => exact Iff.rfl
  | and a₁ a₂ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | or a₁ a₂ ih₁ ih₂ => exact or_congr ih₁ ih₂
  | implies a₁ a₂ ih₁ ih₂ => exact imp_congr ih₁ ih₂
  | ex P ih =>
      exact ⟨fun ⟨x, hx⟩ => ⟨x.down, (ih x.down).mp hx⟩,
        fun ⟨x, hx⟩ => ⟨.up x, (ih x).mpr hx⟩⟩
  | emp => exact Iff.rfl
  | single l bv => cases l; exact Iff.rfl
  | star a₁ a₂ ih₁ ih₂ =>
      constructor
      · rintro ⟨h₁, h₂, rfl, hd, hh₁, hh₂⟩
        exact ⟨h₁, h₂, rfl, hd, ih₁.mp hh₁, ih₂.mp hh₂⟩
      · rintro ⟨h₁, h₂, rfl, hd, hh₁, hh₂⟩
        exact ⟨h₁, h₂, rfl, hd, ih₁.mpr hh₁, ih₂.mpr hh₂⟩
  | «opaque» Λ τ x => exact Iff.rfl

/-! ### Properties: separating conjunction -/

theorem hProp_star_comm {P Q : Asrt} {h : Heap} : HProp h (P ∗ Q) ↔ HProp h (Q ∗ P) := by
  constructor <;>
    · rintro ⟨h₁, h₂, rfl, hdisj, hP, hQ⟩
      exact ⟨h₂, h₁, PFun.union_comm hdisj, hdisj.symm, hQ, hP⟩

theorem hProp_star_assoc {P Q R : Asrt} {h : Heap} :
    HProp h ((P ∗ Q) ∗ R) ↔ HProp h (P ∗ (Q ∗ R)) := by
  constructor
  · rintro ⟨h₁₂, h₃, rfl, hdisj, ⟨h₁, h₂, rfl, hdisj₁₂, hP, hQ⟩, hR⟩
    rw [PFun.disjoint_union_left] at hdisj
    exact ⟨h₁, h₂ ∪ h₃, PFun.union_assoc .., by simp [hdisj₁₂, hdisj.1],
      hP, h₂, h₃, rfl, hdisj.2, hQ, hR⟩
  · rintro ⟨h₁, h₂₃, rfl, hdisj, hP, h₂, h₃, rfl, hdisj₂₃, hQ, hR⟩
    rw [PFun.disjoint_union_right] at hdisj
    exact ⟨h₁ ∪ h₂, h₃, (PFun.union_assoc ..).symm, by simp [hdisj₂₃, hdisj.2],
      ⟨h₁, h₂, rfl, hdisj.1, hP, hQ⟩, hR⟩

theorem sat_and_sat_of_sat_star {P Q : Asrt} (h : Sat (P ∗ Q)) : Sat P ∧ Sat Q := by
  obtain ⟨h, h₁, h₂, rfl, hdisj, hP, hQ⟩ := h
  exact ⟨⟨h₁, hP⟩, ⟨h₂, hQ⟩⟩

/-- Rewriting under the right-hand side of `∗`. -/
theorem hProp_star_congr_right {P Q Q' : Asrt}
    (hQ : ∀ h, HProp h Q ↔ HProp h Q') {h : Heap} :
    HProp h (P ∗ Q) ↔ HProp h (P ∗ Q') := by
  constructor <;>
    · rintro ⟨h₁, h₂, rfl, hdisj, hP, hq⟩
      exact ⟨h₁, h₂, rfl, hdisj, hP, by rw [hQ h₂] at *; exact hq⟩

/-! ### Properties: iterated star -/

theorem hProp_iter_nil {X : Type _} (P : X → Asrt) (h : Heap) :
    HProp h (Asrt.iter ([] : List X) P) ↔ HProp h .emp := Iff.rfl

theorem hProp_iter_cons {X : Type _} (P : X → Asrt) (x : X) (xs : List X) (h : Heap) :
    HProp h (Asrt.iter (x :: xs) P) ↔ HProp h (P x ∗ Asrt.iter xs P) := Iff.rfl

theorem hProp_iter_singleton {X : Type _} (P : X → Asrt) (x : X) (h : Heap) :
    HProp h (Asrt.iter [x] P) ↔ HProp h (P x) := by
  constructor
  · rintro ⟨h₁, h₂, rfl, hdisj, hP, (rfl : h₂ = ∅)⟩
    simpa using hP
  · intro hP
    exact ⟨h, ∅, (PFun.union_empty h).symm, PFun.disjoint_empty_right h, hP, rfl⟩

theorem hProp_iter_append {X : Type _} (P : X → Asrt) (xs ys : List X) (h : Heap) :
    HProp h (Asrt.iter (xs ++ ys) P) ↔ HProp h (Asrt.iter xs P ∗ Asrt.iter ys P) := by
  induction xs generalizing h with
  | nil =>
    simp only [List.nil_append, Asrt.iter_nil]
    constructor
    · intro hys
      exact ⟨∅, h, (PFun.empty_union h).symm, PFun.disjoint_empty_left h, rfl, hys⟩
    · rintro ⟨h₁, h₂, rfl, hdisj, (rfl : h₁ = ∅), hys⟩
      simpa using hys
  | cons a xs ih =>
    simp only [List.cons_append, Asrt.iter_cons]
    exact (hProp_star_congr_right fun h => ih h).trans hProp_star_assoc.symm

theorem hProp_iter_perm {X : Type _} (P : X → Asrt) {xs ys : List X} (h : Heap)
    (hperm : xs.Perm ys) :
    HProp h (Asrt.iter xs P) ↔ HProp h (Asrt.iter ys P) := by
  induction hperm generalizing h with
  | nil => exact Iff.rfl
  | cons a _ ih => exact hProp_star_congr_right fun h => ih h
  | swap a b l =>
    simp only [Asrt.iter_cons]
    constructor <;>
      · rintro ⟨h₁, h₂, rfl, hdisj, hPb, h₃, h₄, rfl, hdisj₂, hPa, hR⟩
        rw [PFun.disjoint_union_right] at hdisj
        refine ⟨h₃, h₁ ∪ h₄, ?_, ?_, hPa, h₁, h₄, rfl, hdisj.2, hPb, hR⟩
        · rw [← PFun.union_assoc, PFun.union_comm hdisj.1, PFun.union_assoc]
        · simp [hdisj.1.symm, hdisj₂]
  | trans _ _ ih₁ ih₂ => exact (ih₁ h).trans (ih₂ h)

theorem exists_hProp_iter_of_subperm {X : Type _} (P : X → Asrt) {xs ys : List X} {h : Heap}
    (hsub : ys.Subperm xs) (hIter : HProp h (Asrt.iter xs P)) :
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ HProp h₁ (Asrt.iter ys P) := by
  obtain ⟨l, hl_perm, hl_sub⟩ := hsub
  obtain ⟨zs, hperm⟩ := hl_sub.exists_perm_append
  rw [hProp_iter_perm P h (hperm.trans (hl_perm.append_right zs)), hProp_iter_append] at hIter
  obtain ⟨h₁, h₂, rfl, hdisj, hys, _⟩ := hIter
  exact ⟨h₁, h₂, rfl, hdisj, hys⟩

theorem exists_hProp_of_mem {X : Type _} (P : X → Asrt) {x : X} {xs : List X} {h : Heap}
    (hin : x ∈ xs) (hIter : HProp h (Asrt.iter xs P)) :
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ HProp h₁ (P x) := by
  obtain ⟨h₁, h₂, rfl, hdisj, hx⟩ :=
    exists_hProp_iter_of_subperm P (List.singleton_subperm_iff.mpr hin) hIter
  exact ⟨h₁, h₂, rfl, hdisj, (hProp_iter_singleton P x h₁).mp hx⟩

/-! ### Properties: weakening -/

theorem hProp_star_pure_weaken (P : Asrt) (Q : Prop) (h : Heap) : HProp h (P ∗ ⌞Q⌟ →ₕ P) := by
  rintro ⟨h₁, h₂, rfl, hdisj, hP, rfl, _⟩
  simpa using hP

theorem hProp_true_star_weaken (P : Asrt) (h : Heap) : HProp h (.true ∗ P →ₕ .true) :=
  fun _ => trivial

theorem hProp_affine_star_weaken (P Q : Asrt) (h : Heap) : HProp h (⌜P⌝ ∗ Q →ₕ ⌜P⌝) := by
  intro hStar
  rw [show HProp h ((P ∗ .true) ∗ Q) ↔ HProp h (P ∗ (.true ∗ Q)) from hProp_star_assoc]
    at hStar
  obtain ⟨h₁, h₂, rfl, hdisj, hP, _⟩ := hStar
  exact ⟨h₁, h₂, rfl, hdisj, hP, trivial⟩

/-! ### Properties: implication -/

theorem hValid_implies_refl (P : Asrt) : ⊨ (P →ₕ P) :=
  fun _ hP => hP

theorem hValid_star_emp_left (P : Asrt) : ⊨ (P ∗ .emp →ₕ P) := by
  rintro h ⟨h₁, h₂, rfl, hdisj, hP, (rfl : h₂ = ∅)⟩
  simpa using hP

theorem hValid_star_emp_right (P : Asrt) : ⊨ (P →ₕ P ∗ .emp) :=
  fun h hP => ⟨h, ∅, (PFun.union_empty h).symm, PFun.disjoint_empty_right h, hP, rfl⟩

/-! ### Properties: opaque resources -/

/-- The state owning the opaque resource of a value is finite: it is reached from the empty
state by running a program. -/
theorem hProp_opaque_finite {Λ : Library} {τ : Ty} {v : Val} {h : Heap}
    (hh : HProp h (.opaque Λ τ v)) : h.dom.Finite := by
  obtain ⟨e, hstep, -⟩ := hh
  exact hstep.dom_finite (by simp)

/-! ### Properties: safe programs -/

theorem safeProgram_subset {𝕍 𝕍' : VarCtx} {Λ : Library} {e : Expr} {τ : Ty}
    (hsafe : SafeProgram 𝕍' Λ τ e) (hsub : 𝕍' ⊆ 𝕍) :
    SafeProgram 𝕍 Λ τ e := by
  induction e generalizing 𝕍 𝕍' τ with
  | pure p => exact checkPure_subset hsafe hsub
  | assume t => exact ⟨checkTerm_subset hsafe.1 hsub, hsafe.2⟩
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, hsafe, hbx⟩ := hsafe
    refine ⟨τ₁, ih₁ hsafe hsub, ?_⟩
    cases bx with
    | anon => exact ih₂ hbx hsub
    | named x => exact ih₂ hbx (PFun.insert_mono _ _ hsub)
  | choice e₁ e₂ ih₁ ih₂ => exact ⟨ih₁ hsafe.1 hsub, ih₂ hsafe.2 hsub⟩
  | call f τs ts =>
    obtain ⟨γ, hγ, hcomp, hsafe, hcheck⟩ := hsafe
    exact ⟨γ, hγ, hcomp, hsafe, checkTerms_subset hcheck hsub⟩
  | _ => trivial

theorem safeProgram_closed {𝕍 : VarCtx} {Λ : Library} {e : Expr} {τ : Ty}
    (hsafe : SafeProgram 𝕍 Λ τ e) : e.Closed 𝕍.dom := by
      induction e generalizing 𝕍 τ
      case pure => exact checkPure_closed hsafe
      case assume => exact checkTerm_closed hsafe.1
      all_goals rcases hsafe with ⟨τ, hsafe⟩
      case letIn =>
        rename_i x _ _ ih₁ ih₂ _
        rcases x with (_ | x) <;> simp_all
        · exact ⟨ih₁ hsafe.1, ih₂ hsafe.2⟩
        · exact ⟨ih₁ hsafe.1, by simpa [PFun.dom_insert] using ih₂ hsafe.2⟩
      case choice => exact ⟨by solve_by_elim, by solve_by_elim⟩
      case call => exact fun t ht => checkTerms_closed hsafe.2.2.2 t ht

/-! ### Type safety of language expressions -/

theorem safe_pure {Λ : Library} {v : Val} :
    SafeMain Λ (v.ty) (.pure (.val v)) := by
  cases v <;> simp only [SafeMain, SafeProgram, CheckPure, CheckTerm,
    Val.ty, Val.baseTy]

theorem safe_call {Λ : Library} {f : Fid} {τs : List Ty} {γ : FunImpl}
      (hinst : Λ.Instantiates f τs γ) (hsafe : γ.safe) :
    SafeProgram (VarCtx.from γ.paramNames (γ.params.map Prod.snd))
      Λ γ.ty (.call f τs (Term.ofVars γ.paramNames)) := by
  refine ⟨γ, hinst, ?_, hsafe, checkTerms_ofVars (by simp [FunImpl.paramNames]) (Λ.instance_params_nodup hinst)⟩
  cases γ.ty <;> simp

end RUXt
