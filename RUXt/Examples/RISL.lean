import RUXt.Semantics.Logic.Poly

namespace RUXt

/-!
# RISL

The RISL proof rules (`WfSpec`), well-formed specification contexts (`WfSpecCtx`), their
soundness, and RISL as a sound logic (`risl`, `risl_sound`).

The rules are stated at an arbitrary universe `u`, about triples `SymTriple.{u} tt` over
telescopes `tt : Tele.{u + 1}`.  The small types of the language are lifted where they occur as
binders: the base rules bind `Lifted Loc`, `Lifted Val`, `Lifted Pure`.  A base rule, whose
telescope contains exactly its used variables, is instantiated at another telescope with
`WfSpec.reindex`.
-/

universe u

/-! ### Function specifications -/

/-- A function specification is parameterised over an arbitrary telescope `tt`
together with a *type projection* `tys : TeleLift tt (List Ty)` and a *value projection*
`vals : TeleLift tt (List Val)`, which read off, for each instantiation of the telescope, the
list of type arguments the function is instantiated at and the list of concrete argument
values it is called with. -/
def FunSpec : Type (u + 2) := (tt : Tele.{u + 1}) × TeleLift tt (List Ty) ×
  TeleLift tt (List Val) × SymAsrt tt × LExit × (Val → SymAsrt tt)

/-- The exit tag of a function specification. -/
def FunSpec.exit : FunSpec.{u} → LExit
  | ⟨_, _, _, _, ε, _⟩ => ε

def SpecCtx := String → List FunSpec.{u}
instance : EmptyCollection SpecCtx.{u} := ⟨fun _ => []⟩

@[simp] theorem SpecCtx.empty_apply (f : String) : (∅ : SpecCtx.{u}) f = [] := rfl

/-- Specification context update. -/
def SpecCtx.update (s : FunSpec.{u}) (f : String) (Γ : SpecCtx.{u}) : SpecCtx.{u} :=
  Function.update Γ f (s :: Γ f)
/-- Specification context inclusion, `Γ [⊆] Γ'`. -/
def SpecCtx.Subseteq (Γ Γ' : SpecCtx.{u}) : Prop := ∀ f, Γ f ⊆ Γ' f
@[inherit_doc] scoped infix:50 " [⊆] " => SpecCtx.Subseteq

theorem SpecCtx.update_apply (Γ : SpecCtx.{u}) (f : String) (s : FunSpec.{u}) :
    Γ.update s f f = s :: Γ f :=
  Function.update_self ..
theorem SpecCtx.update_apply_ne (Γ : SpecCtx.{u}) {f g : String} (s : FunSpec.{u})
    (h : f ≠ g) :
    Γ.update s f g = Γ g :=
  Function.update_of_ne (Ne.symm h) ..

/-! ### Triple notation -/

-- Notation for `WfSpec` where the precondition `P`, the program `e` and the
-- postcondition `Q` are supplied as telescoped functions directly:
-- `Γ ⊢ ⌈P⌉ e ⌈ε, Q⌉`.  The program `e` is parsed at maximal precedence, so an
-- applied `e` must be parenthesised; this both disambiguates the notation and
-- avoids a clash with Mathlib's ceiling notation `⌈·⌉`.
open Lean Parser Term in
scoped syntax:50 (name := wfSpecNotation) term:51 " ⊢ " "⌈" term "⌉ " term:max
  " ⌈" term ", " term "⌉" : term

-- Binder form of the `WfSpec` notation:
-- `Γ ⊢ λₗ args, ⌈P⌉ e ⌈ε : λₗ r, Q⌉`.
-- The telescope binders `args` are written once, immediately after `λₗ`, and are
-- shared by the precondition `P`, the program `e` and (together with the result
-- binder `r`) the postcondition `Q`, so they need not be repeated in each component
-- of the triple.  The telescope itself is synthesised from `args`.  As above, `e`
-- is parsed at maximal precedence.
open Lean Parser Term in
scoped syntax:50 (name := wfSpecBinderNotation) term:51 " ⊢ " "λₗ" (ppSpace funBinder)* ", "
  "⌈" term "⌉ " term:max " ⌈" term " : " "λₗ" ppSpace funBinder ", " term "⌉" : term

macro_rules
  | `($Γ ⊢ ⌈$P⌉ $e ⌈$ε, $Q⌉) => do
      let wf := Lean.mkIdent `RUXt.WfSpec
      `($wf $Γ ⟨$P, $e, $ε, $Q⟩)
  | `($Γ ⊢ λₗ $bs:funBinder*, ⌈$P⌉ $e ⌈$ε : λₗ $r, $Q⌉) => do
      let wf := Lean.mkIdent `RUXt.WfSpec
      let tl ← `([tele $bs*])
      -- the program is written as an `Expr`; the triple stores it lifted into the universe
      -- of the telescope, so the notation inserts the lift.
      if bs.isEmpty then
        `($wf $Γ (tt := $tl) ⟨$P, ULift.up $e, $ε, fun $r => $Q⟩)
      else
        `($wf $Γ (tt := $tl)
          ⟨fun $bs* => $P, fun $bs* => ULift.up $e, $ε, fun $r => fun $bs* => $Q⟩)

/-! ### The RISL proof rules  -/

/-- RISL triples, `Γ ⊢ ⌈P⌉ e ⌈ε, Q⌉`. -/
inductive WfSpec : SpecCtx.{u} → {tt : Tele.{u + 1}} → SymTriple.{u} tt → Prop
  | pure {Γ : SpecCtx} :
      Γ ⊢ λₗ (p : Lifted Pure), ⌈ .emp ⌉ (.pure p.down)
        ⌈ .lok : λₗ r, ⌞ some r = Pure.eval p.down ⌟ ⌉
  | assume {Γ : SpecCtx} :
      Γ ⊢ λₗ , ⌈ .emp ⌉ (.assume .true) ⌈ .lok : λₗ r, ⌞ r = .unit ⌟ ⌉
  | error {Γ : SpecCtx} :
      Γ ⊢ λₗ , ⌈ .emp ⌉ (.error) ⌈ .lerr : λₗ r, ⌞ r = .unit ⌟ ⌉
  | letIn {Γ : SpecCtx} {tt : Tele} {x : Binder} {e₁ e₂ : SymExpr tt}
        {P : SymAsrt tt} {ε : LExit} {Φ Φ' : Val → SymAsrt tt} {v : TeleLift tt Val} :
      (Γ ⊢ ⌈P⌉ e₁ ⌈.lok, Φ'⌉) →
      (Γ ⊢ ⌈teleBind fun args => (Φ' (v.at args)).apply args⌉ (e₂.subst x v) ⌈ε, Φ⌉) →
      (Γ ⊢ ⌈P⌉ (SymExpr.letIn x e₁ e₂) ⌈ε, Φ⌉)
  | let_cut {Γ : SpecCtx} {tt : Tele} {x : Binder} {e₁ e₂ : SymExpr tt}
        {P : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt} :
      (Γ ⊢ ⌈P⌉ e₁ ⌈ε, Φ⌉) → ε ≠ .lok →
      (Γ ⊢ ⌈P⌉ (SymExpr.letIn x e₁ e₂) ⌈ε, Φ⌉)
  | choice {Γ : SpecCtx} {tt : Tele} {eᵢ e₁ e₂ : SymExpr tt}
        {P : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt} :
      (eᵢ = e₁ ∨ eᵢ = e₂) → (Γ ⊢ ⌈P⌉ eᵢ ⌈ε, Φ⌉) →
      (Γ ⊢ ⌈P⌉ (SymExpr.choice e₁ e₂) ⌈ε, Φ⌉)
  | alloc {Γ : SpecCtx} :
      Γ ⊢ λₗ , ⌈ .emp ⌉ (.alloc (.int 1))
        ⌈ .lok : λₗ r, .ex fun l : Lifted Loc => ⌞ r = .loc l.down ⌟ ∗ l.down ↦? ⌉
  -- The three dereferencing commands read their location out of an arbitrary symbolic value
  -- `w`, with the pure fact that `w` *is* the location `l` carried by the pre- and the
  -- postcondition.
  | free {Γ : SpecCtx} :
      Γ ⊢ λₗ (w : Lifted Val) (l : Lifted Loc) (v : Lifted Val),
        ⌈ ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦ v.down ⌉ (.free (.val w.down))
        ⌈ .lok : λₗ r, ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅) ⌉
  | free_uninit {Γ : SpecCtx} :
      Γ ⊢ λₗ (w : Lifted Val) (l : Lifted Loc),
        ⌈ ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦? ⌉ (.free (.val w.down))
        ⌈ .lok : λₗ r, ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅) ⌉
  | free_freed {Γ : SpecCtx} :
      Γ ⊢ λₗ (w : Lifted Val) (l : Lifted Loc),
        ⌈ ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦∅ ⌉ (.free (.val w.down))
        ⌈ .lerr : λₗ r, ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅) ⌉
  | store {Γ : SpecCtx} :
      Γ ⊢ λₗ (w : Lifted Val) (l : Lifted Loc) (v : Lifted Val) (v' : Lifted Val),
        ⌈ ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦ v'.down ⌉
        (.store (.val w.down) (.val v.down))
        ⌈ .lok : λₗ r, ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦ v.down) ⌉
  | store_uninit {Γ : SpecCtx} :
      Γ ⊢ λₗ (w : Lifted Val) (l : Lifted Loc) (v : Lifted Val),
        ⌈ ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦? ⌉
        (.store (.val w.down) (.val v.down))
        ⌈ .lok : λₗ r, ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦ v.down) ⌉
  | store_freed {Γ : SpecCtx} :
      Γ ⊢ λₗ (w : Lifted Val) (l : Lifted Loc) (v : Lifted Val),
        ⌈ ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦∅ ⌉
        (.store (.val w.down) (.val v.down))
        ⌈ .lerr : λₗ r, ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅) ⌉
  | load {Γ : SpecCtx} :
      Γ ⊢ λₗ (w : Lifted Val) (l : Lifted Loc) (v : Lifted Val),
        ⌈ ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦ v.down ⌉ (.load (.val w.down))
        ⌈ .lok : λₗ r, ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = v.down ⌟ ∗ l.down ↦ v.down) ⌉
  | load_uninit {Γ : SpecCtx} :
      Γ ⊢ λₗ (w : Lifted Val) (l : Lifted Loc),
        ⌈ ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦? ⌉ (.load (.val w.down))
        ⌈ .lerr : λₗ r, ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦?) ⌉
  | load_freed {Γ : SpecCtx} :
      Γ ⊢ λₗ (w : Lifted Val) (l : Lifted Loc),
        ⌈ ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦∅ ⌉ (.load (.val w.down))
        ⌈ .lerr : λₗ r, ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅) ⌉
  | frame {Γ : SpecCtx} {tt : Tele} {e : SymExpr tt}
        {P R : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt} :
      (Γ ⊢ ⌈P⌉ e ⌈ε, Φ⌉) →
      (Γ ⊢ ⌈teleBind fun args => R.apply args ∗ P.apply args⌉ e
        ⌈ε, fun v => teleBind fun args => R.apply args ∗ (Φ v).apply args⌉)
  | disj {Γ : SpecCtx} {tt : Tele} {e : SymExpr tt}
        {P₁ P₂ : SymAsrt tt} {ε : LExit} {Φ₁ Φ₂ : Val → SymAsrt tt} :
      (Γ ⊢ ⌈P₁⌉ e ⌈ε, Φ₁⌉) → (Γ ⊢ ⌈P₂⌉ e ⌈ε, Φ₂⌉) →
      (Γ ⊢ ⌈teleBind fun args => P₁.apply args ∨ₕ P₂.apply args⌉ e
        ⌈ε, fun v => teleBind fun args => (Φ₁ v).apply args ∨ₕ (Φ₂ v).apply args⌉)
  -- The conclusion may only rename the program along the telescope map `f`: the two programs
  -- have to agree at *every* instantiation of the telescope, whether or not the assertions
  -- of the triple are satisfiable there.
  | cons {Γ Γ' : SpecCtx} {tt tt' : Tele}
        {P : SymAsrt tt} {e : SymExpr tt} {Φ : Val → SymAsrt tt}
        {P' : SymAsrt tt'} {e' : SymExpr tt'} {Φ' : Val → SymAsrt tt'}
        {ε : LExit} (f : TeleArg tt → TeleArg tt') :
      Γ' [⊆] Γ →
      (∀ args, ⊨ (P'.apply (f args) →ₕ P.apply args)) →
      (∀ v args, ⊨ (Φ v).apply args →ₕ (Φ' v).apply (f args)) →
      (∀ args, e.at args = e'.at (f args)) →
      (Γ' ⊢ ⌈P'⌉ e' ⌈ε, Φ'⌉) →
      (Γ ⊢ ⌈P⌉ e ⌈ε, Φ⌉)
  | ex {Γ : SpecCtx} {tt : Tele} {X : Type u} {e : SymExpr tt}
        {P : SymAsrt (Tele.cons (fun _ : ULift.{u + 1, u} X => tt))} {ε : LExit}
        {Φ : Val → SymAsrt (Tele.cons (fun _ : ULift.{u + 1, u} X => tt))} :
      (Γ ⊢ ⌈P⌉ (e.reindex Sigma.snd) ⌈ε, Φ⌉) →
      (Γ ⊢ ⌈teleBind fun args => .ex fun x : X => P.apply ⟨.up x, args⟩⌉ e
        ⌈ε, fun v => teleBind fun args => .ex fun x : X => (Φ v).apply ⟨.up x, args⟩⌉)
  | call {Γ : SpecCtx} {tt : Tele} {f : String} {tys : TeleLift tt (List Ty)}
      {vals : TeleLift tt (List Val)}
      {P : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt} :
      (⟨tt, tys, vals, P, ε, Φ⟩ : FunSpec) ∈ Γ f →
      (Γ ⊢ ⌈P⌉ (SymExpr.call f tys vals) ⌈ε, Φ⌉)

/-- Re-index a derivation along a telescope map `f : TeleArg tt' → TeleArg tt`.
This is the special case of the (generalised) Consequence rule that only changes
the telescope, leaving the underlying assertions and program untouched (up to the
reindexing). -/
theorem WfSpec.reindex {Γ : SpecCtx.{u}} {tt tt' : Tele.{u + 1}} {e : SymExpr tt}
    {P : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt}
    (f : TeleArg tt' → TeleArg tt) (h : Γ ⊢ ⌈P⌉ e ⌈ε, Φ⌉) :
    Γ ⊢ ⌈teleBind fun args => P.apply (f args)⌉ (e.reindex f)
        ⌈ε, fun r => teleBind fun args => (Φ r).apply (f args)⌉ :=
  .cons f (fun _ => List.Subset.refl _)
    (fun args => by rw [teleBind_apply]; exact hValid_implies_refl _)
    (fun r args => by rw [teleBind_apply]; exact hValid_implies_refl _)
    (fun args => by rw [SymExpr.reindex_at])
    h

/-- Well-formed specification contexts, `γ ≺ₛ Γ`.

A specification of `f` is recorded once the body of the declaration `φ` the library maps `f`
to has been derived for it.  The type arguments `tys` and the argument values `vals` the
specification speaks of are *well-sized* tuples — `φ.tyArity` types and one value per
parameter of `φ` — so the body premise is simply the triple for the implementation `φ` gives
at those types (`FunDecl.concretise`), run with those values (`FunImpl.with`).  The context
stores the lists those tuples map to. -/
inductive WfSpecCtx (Λ : Library) : SpecCtx.{u} → Prop
  | empty :
      WfSpecCtx Λ ∅
  | update {Γ Γ' : SpecCtx} {tt : Tele} {f : Fid} {φ : FunDecl}
        {tys : TeleLift tt φ.TyArgs} {vals : TeleLift tt φ.ValArgs}
        {P : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt} :
      WfSpecCtx Λ Γ →
      Γ' = Γ.update ⟨tt, tys.toListLift, vals.toListLift, P, ε, Φ⟩ f →
      Λ.MapsTo f φ →
      (Γ ⊢ ⌈P⌉ (SymExpr.body φ tys vals) ⌈ε, Φ⌉) →
      WfSpecCtx Λ Γ'
@[inherit_doc] scoped infix:50 " ≺ₛ " => WfSpecCtx

/-! ### Soundness of RISL -/

/-- The under-approximate call triple associated to a function specification. -/
def FunSpec.callTriple (f : String) : (s : FunSpec.{u}) → SymTriple.{u} s.1
  | ⟨_, tys, vals, P, ε, Φ⟩ => ⟨P, SymExpr.call f tys vals, ε, Φ⟩

/-- A specification context *never mentions the `lmiss` exit tag*.  Contexts built
by `WfSpecCtx` enjoy this property, which is what makes the frame rule sound. -/
def SpecCtxNoMiss (Γ : SpecCtx.{u}) : Prop :=
  ∀ (f : String) (s : FunSpec.{u}), s ∈ Γ f → s.exit ≠ .lmiss

/-- A specification context is *semantically sound* when every stored
specification yields a valid under-approximate call triple. -/
def SoundSpecCtx (Λ : Library) (Γ : SpecCtx.{u}) : Prop :=
  ∀ (f : String) (s : FunSpec.{u}), s ∈ Γ f → UXFrameTriple Λ (s.callTriple f)

theorem SpecCtxNoMiss.mono {Γ Γ' : SpecCtx.{u}}
    (hsub : Γ' [⊆] Γ) (h : SpecCtxNoMiss Γ) : SpecCtxNoMiss Γ' :=
  fun f s hmem => h f s (hsub f hmem)

theorem SoundSpecCtx.mono {Λ : Library} {Γ Γ' : SpecCtx.{u}}
    (hsub : Γ' [⊆] Γ) (h : SoundSpecCtx Λ Γ) : SoundSpecCtx Λ Γ' :=
  fun f s hmem => h f s (hsub f hmem)

/-- No RISL derivation over a `lmiss`-free context ends in the `lmiss` tag. -/
theorem WfSpec.exit_ne_lmiss {Γ : SpecCtx.{u}} {tt : Tele.{u + 1}} {triple : SymTriple.{u} tt}
    (h : WfSpec Γ triple) : SpecCtxNoMiss Γ → triple.exit ≠ .lmiss := by
  induction h <;> try tauto
  rename_i hsub _ _ _ _ hmiss
  exact fun h => hmiss (SpecCtxNoMiss.mono hsub h)

/-- A sound call triple can be recovered from a sound body triple. -/
theorem callTriple_of_body {Λ : Library} {f : String} {φ : FunDecl}
    {tt : Tele.{u + 1}} {tys : TeleLift tt φ.TyArgs} {vals : TeleLift tt φ.ValArgs}
    {P : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt}
    (hmaps : Λ.MapsTo f φ)
    (hbody : UXFrameTriple Λ ⟨P, SymExpr.body φ tys vals, ε, Φ⟩) :
    UXFrameTriple Λ ⟨P, SymExpr.call f tys.toListLift vals.toListLift, ε, Φ⟩ := by
  intro args v h' hΦ
  obtain ⟨h, hP, εₛ, hε, hstep⟩ := hbody args v h' hΦ
  rw [SymExpr.body_at] at hstep
  refine ⟨h, hP, εₛ, hε, ?_⟩
  rw [SymExpr.call_at, teleLift_at, teleLift_at]
  exact .call (Λ.instantiates_concretise hmaps (tys.at args)) hstep

/-! #### Soundness of the individual structural proof rules -/

/-- Soundness of the sequencing rule `letIn`. -/
theorem uxFrameTriple_letIn {Λ : Library} {tt : Tele.{u + 1}} {x : Binder} {e₁ e₂ : SymExpr tt}
    {P : SymAsrt tt} {ε : LExit} {Φ Φ' : Val → SymAsrt tt} {v : TeleLift tt Val}
    (h₁ : UXFrameTriple Λ ⟨P, e₁, .lok, Φ'⟩)
    (h₂ : UXFrameTriple Λ ⟨teleBind fun args => (Φ' (v.at args)).apply args,
      e₂.subst x v, ε, Φ⟩) :
    UXFrameTriple Λ ⟨P, SymExpr.letIn x e₁ e₂, ε, Φ⟩ := by
  intro args r h' hΦ
  obtain ⟨h'', hΦ', ε₂, hε₂, hstep₂⟩ := h₂ args r h' hΦ
  rw [teleBind_apply] at hΦ'
  rw [SymExpr.subst_at] at hstep₂
  obtain ⟨h, hP, ε₁, ⟨⟩, hstep₁⟩ := h₁ args (v.at args) h'' hΦ'
  rw [SymExpr.letIn_at]
  exact ⟨h, hP, ε₂, hε₂, .letIn hstep₁ hstep₂⟩

/-- Soundness of the short-circuiting sequencing rule `let_cut`. -/
theorem uxFrameTriple_let_cut {Λ : Library} {tt : Tele.{u + 1}} {x : Binder} {e₁ e₂ : SymExpr tt}
    {P : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt}
    (h : UXFrameTriple Λ ⟨P, e₁, ε, Φ⟩) (hne : ε ≠ .lok) :
    UXFrameTriple Λ ⟨P, SymExpr.letIn x e₁ e₂, ε, Φ⟩ := by
  intro args r h' hΦ
  obtain ⟨h, hP, εₛ, hε, hstep⟩ := h args r h' hΦ
  simp [SymExpr.letIn_at]
  refine' ⟨h, hP, εₛ, hε, FrameStep.let_cut hstep _⟩
  cases ε <;> cases r <;> simp_all [LExit.toExit]
  · intro x; subst hε; simp
  · intro x; subst hε; simp

/-- Soundness of the nondeterministic choice rule `choice`. -/
theorem uxFrameTriple_choice {Λ : Library} {tt : Tele.{u + 1}} {eᵢ e₁ e₂ : SymExpr tt}
    {P : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt}
    (he : eᵢ = e₁ ∨ eᵢ = e₂) (h : UXFrameTriple Λ ⟨P, eᵢ, ε, Φ⟩) :
    UXFrameTriple Λ ⟨P, SymExpr.choice e₁ e₂, ε, Φ⟩ := by
  intro args r h' hΦ
  obtain ⟨h, hP, εₛ, hε, hstep⟩ := h args r h' hΦ
  simp_all [SymExpr.choice_at]
  rcases he with ⟨rfl⟩ | ⟨rfl⟩
  · exact ⟨h, hP, .choice hstep (Or.inl rfl)⟩;
  · exact ⟨h, hP, .choice hstep (Or.inr rfl)⟩

/-- Soundness of the frame rule, for an exit tag other than `lmiss`. -/
theorem uxFrameTriple_frame {Λ : Library} {tt : Tele.{u + 1}} {R : SymAsrt tt} {e : SymExpr tt}
    {P : SymAsrt tt} {ε : LExit} {Φ : Val → SymAsrt tt}
    (hne : ε ≠ .lmiss)
    (h : UXFrameTriple Λ ⟨P, e, ε, Φ⟩) :
    UXFrameTriple Λ ⟨teleBind fun args => R.apply args ∗ P.apply args, e, ε,
      fun v => teleBind fun args => R.apply args ∗ (Φ v).apply args⟩ := by
  intro args v h' hΦ
  rw [teleBind_apply] at *
  obtain ⟨hR, hpost, rfl, hdisj, ⟨hhR, hhpost⟩⟩ := hΦ
  obtain ⟨hpre, hP, εₛ, hε, hstep⟩ := h args v hpost hhpost
  obtain ⟨hstepF, hdisj'⟩ | ⟨l, rfl, hdom⟩ := frame_addition hstep hR hdisj.symm
  · refine ⟨hR ∪ hpre, ⟨hR, hpre, rfl, hdisj'.symm, hhR, hP⟩, εₛ, hε, ?_⟩
    rwa [PFun.union_comm hdisj'.symm, PFun.union_comm hdisj]
  · cases ε <;> simp_all [LExit.toExit]
    cases v <;> cases hε

/-- Soundness of the disjunction rule. -/
theorem uxFrameTriple_disj {Λ : Library} {tt : Tele.{u + 1}} {e : SymExpr tt}
    {P₁ P₂ : SymAsrt tt} {ε : LExit} {Φ₁ Φ₂ : Val → SymAsrt tt}
    (h₁ : UXFrameTriple Λ ⟨P₁, e, ε, Φ₁⟩)
    (h₂ : UXFrameTriple Λ ⟨P₂, e, ε, Φ₂⟩) :
    UXFrameTriple Λ ⟨teleBind fun args => P₁.apply args ∨ₕ P₂.apply args, e, ε,
      fun v => teleBind fun args => (Φ₁ v).apply args ∨ₕ (Φ₂ v).apply args⟩ := by
  intro args v h' hΦ
  simp_all [teleBind_apply]
  rcases hΦ with ⟨hΦ₁⟩ | ⟨hΦ₂⟩
  · obtain ⟨h, hP₁, εₛ, hε, hstep⟩ := h₁ args v h' hΦ₁
    exact ⟨h, Or.inl hP₁, εₛ, hε, hstep⟩
  · obtain ⟨h, hP₂, εₛ, hε, hstep⟩ := h₂ args v h' hΦ₂
    exact ⟨h, Or.inr hP₂, εₛ, hε, hstep⟩

/-- Soundness of the existential rule. -/
theorem uxFrameTriple_ex {Λ : Library} {tt : Tele.{u + 1}} {X : Type u} {e : SymExpr tt}
    {P : SymAsrt (Tele.cons (fun _ : ULift.{u + 1, u} X => tt))} {ε : LExit}
    {Φ : Val → SymAsrt (Tele.cons (fun _ : ULift.{u + 1, u} X => tt))}
    (h : UXFrameTriple Λ ⟨P, e.reindex Sigma.snd, ε, Φ⟩) :
    UXFrameTriple Λ ⟨teleBind fun args => .ex fun x : X => P.apply ⟨.up x, args⟩, e, ε,
      fun v => teleBind fun args => .ex fun x : X => (Φ v).apply ⟨.up x, args⟩⟩ := by
  intro args v h' hΦ
  rw [teleBind_apply] at hΦ
  obtain ⟨x, hx⟩ := hΦ
  obtain ⟨h, hh, εₛ, hε, hstep⟩ := h ⟨.up x, args⟩ v h' hx
  rw [SymExpr.reindex_at] at hstep
  exact ⟨h, by rw [teleBind_apply]; exact ⟨x, hh⟩, εₛ, hε, hstep⟩

/-- Soundness of the (generalised) consequence rule. -/
theorem uxFrameTriple_cons {Λ : Library} {tt tt' : Tele.{u + 1}} {e : SymExpr tt} {e' : SymExpr tt'}
    {P : SymAsrt tt} {P' : SymAsrt tt'} {ε : LExit}
    {Φ : Val → SymAsrt tt} {Φ' : Val → SymAsrt tt'}
    (f : TeleArg tt → TeleArg tt')
    (hpre : ∀ args, ⊨ (P'.apply (f args) →ₕ P.apply args))
    (hpost : ∀ v args, ⊨ (Φ v).apply args →ₕ (Φ' v).apply (f args))
    (hexpr : ∀ args, e.at args = e'.at (f args))
    (h : UXFrameTriple Λ ⟨P', e', ε, Φ'⟩) :
    UXFrameTriple Λ ⟨P, e, ε, Φ⟩ := by
  intro args v h' hΦ
  obtain ⟨hh, hP', ⟨εₛ, hε, hstep⟩⟩ := h (f args) v h' (hpost v args h' hΦ)
  exact ⟨hh, hpre args hh hP', εₛ, hε, by rw [hexpr args]; exact hstep⟩

/-! #### Soundness of the individual atomic-command proof rules -/

/-- Soundness of the `pure` rule. -/
theorem uxFrameTriple_pure {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Lifted.{u + 1} Pure)]) Λ ⟨fun _ => .emp,
      fun p => .up (.pure p.down),
      .lok, fun r p => ⌞ some r = Pure.eval p.down ⌟⟩ := by
  rintro p r h' ⟨rfl, hΦ⟩
  simp_all [TeleFun.apply]
  exact ⟨_, rfl, .pure hΦ.symm⟩

/-- Soundness of the `assume` rule. -/
theorem uxFrameTriple_assume {Λ : Library} :
    UXFrameTriple (tt := [tele]) Λ ⟨.emp, .up (.assume .true),
      .lok, fun r => ⌞ r = .unit ⌟⟩ := by
  rintro args v h' ⟨rfl, rfl⟩
  exact ⟨∅, by tauto, .ok .unit, rfl, .assume⟩

/-- Soundness of the `error` rule. -/
theorem uxFrameTriple_error {Λ : Library} :
    UXFrameTriple (tt := [tele]) Λ ⟨.emp, .up .error,
      .lerr, fun r => ⌞ r = .unit ⌟⟩ := by
  rintro args v h' ⟨rfl, rfl⟩
  exact ⟨∅, by tauto, .err, rfl, .error⟩

/-- Soundness of the `alloc` rule. -/
theorem uxFrameTriple_alloc {Λ : Library} :
    UXFrameTriple (tt := [tele]) Λ ⟨.emp, .up (.alloc (.int 1)),
      .lok, fun r => .ex fun l : Lifted.{u} Loc => ⌞ r = .loc l.down ⌟ ∗ l.down ↦?⟩ := by
  intro r h' h''
  simp [TeleFun.apply]
  rintro x rfl rfl
  exact ⟨_, rfl, .alloc rfl id rfl rfl⟩

/-- Soundness of the `free` rule. -/
theorem uxFrameTriple_free {Λ : Library} :
    UXFrameTriple
      (tt := [tele (_ : Lifted.{u + 1} Val) (_ : Lifted.{u + 1} Loc) (_ : Lifted.{u + 1} Val)]) Λ
    ⟨fun w l v => ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦ v.down,
    fun w _ _ => .up (.free (.val w.down)),
    .lok, fun r w l _ => ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅)⟩ := by
  intro ⟨⟨w⟩, ⟨l⟩, ⟨v'⟩, ⟨⟩⟩ v h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .free rfl ?mapsTo hΦ.2.2.2 ?iDom ?hFreed⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case iDom =>
    simp
  case hFreed =>
    simp only [PFun.singleton, Heap.free, Heap.update, PFun.insert_insert_self]

/-- Soundness of the `free_uninit` rule. -/
theorem uxFrameTriple_free_uninit {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Lifted.{u + 1} Val) (_ : Lifted.{u + 1} Loc)]) Λ
      ⟨fun w l => ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦?,
      fun w _ => .up (.free (.val w.down)),
      .lok, fun r w l => ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅)⟩ := by
  intro ⟨⟨w⟩, ⟨l⟩, ⟨⟩⟩ r h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .free rfl ?mapsTo hΦ.2.2.2 ?iDom ?hFreed⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case iDom =>
    simp
  case hFreed =>
    simp only [PFun.singleton, Heap.free, Heap.update, PFun.insert_insert_self]

/-- Soundness of the `free_freed` rule. -/
theorem uxFrameTriple_free_freed {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Lifted.{u + 1} Val) (_ : Lifted.{u + 1} Loc)]) Λ
      ⟨fun w l => ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦∅,
      fun w _ => .up (.free (.val w.down)), .lerr,
      fun r w l => ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅)⟩ := by
  intro ⟨⟨w⟩, ⟨l⟩, ⟨⟩⟩ r h' hΦ
  simp_all [TeleFun.apply]
  exact ⟨_, rfl, .free_err rfl (by simp [Heap.MapsTo, PFun.singleton])⟩

/-- Soundness of the `store` rule. -/
theorem uxFrameTriple_store {Λ : Library} :
    UXFrameTriple
      (tt := [tele (_ : Lifted.{u + 1} Val) (_ : Lifted.{u + 1} Loc) (_ : Lifted.{u + 1} Val)
        (_ : Lifted.{u + 1} Val)]) Λ
      ⟨fun w l _ v' => ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦ v'.down,
      fun w _ v _ => .up (.store (.val w.down) (.val v.down)),
      .lok, fun r w l v _ => ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦ v.down)⟩ := by
  intro ⟨⟨w⟩, ⟨l⟩, ⟨v⟩, ⟨v'⟩, ⟨⟩⟩ r h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .store rfl rfl ?mapsTo ?iDom ?vStored⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case iDom =>
    simp [hΦ.2.2]
  case vStored =>
    simp only [hΦ.2.2, Heap.store, Heap.update, BlockHeap.update,
      PFun.singleton, PFun.insert_insert_self]

/-- Soundness of the `store_uninit` rule. -/
theorem uxFrameTriple_store_uninit {Λ : Library} :
    UXFrameTriple
      (tt := [tele (_ : Lifted.{u + 1} Val) (_ : Lifted.{u + 1} Loc) (_ : Lifted.{u + 1} Val)]) Λ
      ⟨fun w l _ => ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦?,
      fun w _ v => .up (.store (.val w.down) (.val v.down)),
      .lok, fun r w l v => ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦ v.down)⟩ := by
  intro ⟨⟨w⟩, ⟨l⟩, ⟨v⟩, ⟨⟩⟩ r h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .store rfl rfl ?mapsTo ?iDom ?vStored⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case iDom =>
    simp [hΦ.2.2]
  case vStored =>
    simp only [hΦ.2.2, Heap.store, Heap.update, BlockHeap.update,
      PFun.singleton, PFun.insert_insert_self]

/-- Soundness of the `store_freed` rule. -/
theorem uxFrameTriple_store_freed {Λ : Library} :
    UXFrameTriple
      (tt := [tele (_ : Lifted.{u + 1} Val) (_ : Lifted.{u + 1} Loc) (_ : Lifted.{u + 1} Val)]) Λ
      ⟨fun w l _ => ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦∅,
      fun w _ v => .up (.store (.val w.down) (.val v.down)),
      .lerr, fun r w l _ => ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅)⟩ := by
  intro ⟨⟨w⟩, ⟨l⟩, ⟨v⟩, _⟩ r h' hΦ
  simp_all [TeleFun.apply]
  exact ⟨_, rfl, .store_err rfl (by simp [Heap.MapsTo, PFun.singleton])⟩

/-- Soundness of the `load` rule. -/
theorem uxFrameTriple_load {Λ : Library} :
    UXFrameTriple
      (tt := [tele (_ : Lifted.{u + 1} Val) (_ : Lifted.{u + 1} Loc) (_ : Lifted.{u + 1} Val)]) Λ
      ⟨fun w l v => ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦ v.down,
      fun w _ _ => .up (.load (.val w.down)), .lok,
      fun r w l v => ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = v.down ⌟ ∗ l.down ↦ v.down)⟩ := by
  intro ⟨⟨w⟩, ⟨l⟩, ⟨v'⟩, ⟨⟩⟩ v h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .load rfl ?mapsTo ?vLoaded⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case vLoaded =>
    simp [BlockHeap.MapsTo, hΦ.2.2]

/-- Soundness of the `load_uninit` rule. -/
theorem uxFrameTriple_load_uninit {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Lifted.{u + 1} Val) (_ : Lifted.{u + 1} Loc)]) Λ
      ⟨fun w l => ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦?,
      fun w _ => .up (.load (.val w.down)), .lerr,
      fun r w l => ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦?)⟩ := by
  intro ⟨⟨w⟩, ⟨l⟩, ⟨⟩⟩ v h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .load_err_block rfl ?mapsTo ?vLoaded⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case vLoaded =>
    simp [BlockHeap.MapsTo, hΦ.2.2]

/-- Soundness of the `load_freed` rule. -/
theorem uxFrameTriple_load_freed {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Lifted.{u + 1} Val) (_ : Lifted.{u + 1} Loc)]) Λ
      ⟨fun w l => ⌞ w.down = .loc l.down ⌟ ∗ l.down ↦∅,
      fun w _ => .up (.load (.val w.down)), .lerr,
      fun r w l => ⌞ w.down = .loc l.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l.down ↦∅)⟩ := by
  intro ⟨⟨w⟩, ⟨l⟩, ⟨⟩⟩ v h' hΦ
  simp_all [TeleFun.apply]
  exact ⟨_, rfl, .load_err rfl (by simp [Heap.MapsTo, PFun.singleton])⟩

/-- Soundness of the RISL proof rules relative to a sound, `lmiss`-free
specification context. -/
theorem WfSpec.sound {Λ : Library} {tt : Tele.{u + 1}} {Γ : SpecCtx.{u}}
    {triple : SymTriple.{u} tt}
    (h : WfSpec Γ triple) :
    SpecCtxNoMiss Γ → SoundSpecCtx Λ Γ → UXFrameTriple Λ triple := by
  induction h with
  | pure => exact fun _ _ => uxFrameTriple_pure
  | assume => exact fun _ _ => uxFrameTriple_assume
  | error => exact fun _ _ => uxFrameTriple_error
  | letIn h₁ h₂ ih₁ ih₂ => exact fun hnm hΓ => uxFrameTriple_letIn (ih₁ hnm hΓ) (ih₂ hnm hΓ)
  | let_cut h hne ih => exact fun hnm hΓ => uxFrameTriple_let_cut (ih hnm hΓ) hne
  | choice he h ih => exact fun hnm hΓ => uxFrameTriple_choice he (ih hnm hΓ)
  | alloc => exact fun _ _ => uxFrameTriple_alloc
  | free => exact fun _ _ => uxFrameTriple_free
  | free_uninit => exact fun _ _ => uxFrameTriple_free_uninit
  | free_freed => exact fun _ _ => uxFrameTriple_free_freed
  | store => exact fun _ _ => uxFrameTriple_store
  | store_uninit => exact fun _ _ => uxFrameTriple_store_uninit
  | store_freed => exact fun _ _ => uxFrameTriple_store_freed
  | load => exact fun _ _ => uxFrameTriple_load
  | load_uninit => exact fun _ _ => uxFrameTriple_load_uninit
  | load_freed => exact fun _ _ => uxFrameTriple_load_freed
  | frame h ih => exact fun hnm hΓ => uxFrameTriple_frame (h.exit_ne_lmiss hnm) (ih hnm hΓ)
  | disj h₁ h₂ ih₁ ih₂ => exact fun hnm hΓ => uxFrameTriple_disj (ih₁ hnm hΓ) (ih₂ hnm hΓ)
  | cons f hsub hpre hpost hexpr h ih =>
      exact fun hnm hΓ =>
        uxFrameTriple_cons f hpre hpost hexpr (ih (hnm.mono hsub) (hΓ.mono hsub))
  | ex h ih => exact fun hnm hΓ => uxFrameTriple_ex (ih hnm hΓ)
  | call hmem => exact fun _ hΓ => hΓ _ _ hmem

/-- Soundness of well-formed specification contexts: they are both `lmiss`-free and semantically sound. -/
theorem WfSpecCtx.sound {Λ : Library} {Γ : SpecCtx.{u}} (h : Λ ≺ₛ Γ) :
    SpecCtxNoMiss Γ ∧ SoundSpecCtx Λ Γ := by
  induction h with
  | empty => simp [SpecCtxNoMiss, SoundSpecCtx]
  | @update _ _ _ f _ _ _ _ _ _ _ _ hmaps hspec hctx =>
    obtain ⟨hmiss, hctx⟩ := hctx
    simp_all [SpecCtxNoMiss, SoundSpecCtx]
    refine ⟨?_, ?_⟩ <;> intro f' s hin <;>
      by_cases hf : f' = f <;> simp_all [SpecCtx.update]
    · subst hf
      rw [Function.update_self] at hin
      rcases List.mem_cons.1 hin with rfl | hin
      · exact hspec.exit_ne_lmiss hmiss
      · exact hmiss _ _ hin
    · exact hmiss _ _ hin
    · subst hf
      rw [Function.update_self] at hin
      rcases List.mem_cons.1 hin with rfl | hin
      · exact callTriple_of_body hmaps (hspec.sound hmiss hctx)
      · exact hctx _ _ hin

/-! ### RISL as a logic -/

/-- RISL as a UX logic. -/
def risl : Logic where
  DerivableSpec Λ triple := ∃ Γ, Λ ≺ₛ Γ ∧ WfSpec Γ triple

/-- RISL is a sound logic: every triple it derives is an under-approximate triple of the
instrumented semantics. -/
theorem risl_sound : risl.Sound := by
  intro tt Λ triple ⟨Γ, hctx, hwf⟩
  obtain ⟨hnm, hsound⟩ := hctx.sound
  exact hwf.sound hnm hsound

end RUXt
