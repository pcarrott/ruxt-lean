import RUXt.Semantics.Logic.Asrt

/-!
# Under-approximate semantics of symbolic triples, and sound logics

The under-approximate reading of a symbolic triple, for the instrumented (`UXFrameTriple`) and
the full (`UXFullTriple`) operational semantics, the relation between the two, and soundness of
a logic (`Logic.Sound`).
-/

namespace RUXt

universe u

/-! ### Exit tags -/

/-- The exit tag of a triple. -/
def SymTriple.exit {tt : Tele.{u + 1}} : SymTriple tt → LExit
  | ⟨_, _, ε, _⟩ => ε

/-- The semantic exit a logical tag stands for at a result value, or `none` when the value
does not fit the tag. -/
def LExit.toExit : LExit → Val → Option Exit
  | .lok, v => some (.ok v)
  | .lerr, .unit => some .err
  | .lmiss, .loc l => some (.miss l)
  | _, _ => none

/-! ### UX semantics -/

/-- Under-approximate semantic triples for a given big-step relation. -/
def UXTriple {tt : Tele.{u + 1}} (step : Library → Heap → Expr → Heap → Exit → Prop)
    : Library → SymTriple.{u} tt → Prop
  | Λ, ⟨P, e, εₗ, Φ⟩ =>
    ∀ args v h', HProp h' ((Φ v).apply args) → ∃ h, HProp h (P.apply args) ∧
    ∃ εₛ, εₗ.toExit v = some εₛ ∧ step Λ h (e.at args) h' εₛ
/-- Under-approximate semantic triples for the instrumented semantics. -/
def UXFrameTriple {tt : Tele.{u + 1}} : Library → SymTriple.{u} tt → Prop := UXTriple FrameStep
/-- Under-approximate semantic triples for the full semantics. -/
def UXFullTriple {tt : Tele.{u + 1}} : Library → SymTriple.{u} tt → Prop := UXTriple BigStep

/-- Maps a triple with a `miss` exit to one with an `err` exit, the missing location (lifted
into `Type u`) being existentially quantified. -/
def mapMissToErr {tt : Tele.{u + 1}} : SymTriple.{u} tt → SymTriple.{u} tt
  | ⟨P, e, .lmiss, Φ⟩ => ⟨P, e, .lerr, fun v => teleBind (fun args =>
      ⌞ v = .unit ⌟ ∗ .ex fun l : ULift.{u, 0} Loc => (Φ (.loc l.down)).apply args)⟩
  | triple => triple
/-- Preserved behaviour between the instrumented and the full triples. -/
theorem uxFullTriple_of_uxFrameTriple {tt : Tele.{u + 1}} {Λ : Library} {triple : SymTriple.{u} tt}
    (hux : UXFrameTriple Λ triple) : UXFullTriple Λ (mapMissToErr triple) := by
  intro args v h' hΦ
  obtain ⟨P, e, εₗ, Φ⟩ := triple
  cases εₗ <;> simp [*] at *
  · obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    obtain hstep := semantics_preservation hstep
    cases Hε
    exact ⟨h, hP, .ok v, rfl, hstep⟩
  · obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    obtain hstep := semantics_preservation hstep
    let .unit := v
    cases Hε
    exact ⟨h, hP, .err, rfl, hstep⟩
  · rw [teleBind_apply] at hΦ
    obtain ⟨h1', h', rfl, hdisj, ⟨rfl, rfl⟩, hΦ⟩ := hΦ
    rw [<- PFun.eq_empty_union]
    obtain ⟨⟨l⟩, hΦ⟩ := hΦ
    obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    obtain hstep := semantics_preservation hstep
    cases Hε
    exact ⟨h, hP, .err, rfl, hstep⟩

theorem uxFrameTriple_spec {tt : Tele.{u + 1}} {Λ : Library}
    {P : SymAsrt tt} {e : SymExpr tt} {εₗ : LExit} {Φ : Val → SymAsrt tt}
    (hux : UXFrameTriple Λ ⟨P, e, εₗ, Φ⟩) :
    ∀ args r h', HProp h' ((Φ r).apply args) → ∀ ε, εₗ.toExit r = some ε →
    ∃ h, HProp h (P.apply args) ∧ Λ ⊢ ⟨ h | e.at args ⟩ ⇓ᵢ ⟨ h' | ε ⟩ := by
  intro args r h' hΦ ε hε
  cases εₗ
  · cases hε
    obtain ⟨h, hP, ε, ⟨⟩, hstep⟩ := hux _ _ _ hΦ
    exact ⟨h, hP, hstep⟩
  · let .unit := r; cases hε
    obtain ⟨h, hP, ε, ⟨⟩, hstep⟩ := hux _ _ _ hΦ
    exact ⟨h, hP, hstep⟩
  · let .loc l := r; cases hε
    specialize hux args (.loc l) h' hΦ
    obtain ⟨h, hP, ε, ⟨⟩, hstep⟩ := hux
    exact ⟨h, hP, hstep⟩

/-! ### Sound logics -/

/-- A logic is *sound* when every specification it derives is an under-approximate triple of
the instrumented semantics. -/
def Logic.Sound (L : Logic.{u}) : Prop :=
  ∀ {tt : Tele.{u + 1}} {Λ : Library} {triple : SymTriple.{u} tt},
    L.DerivableSpec Λ triple → UXFrameTriple Λ triple

end RUXt
