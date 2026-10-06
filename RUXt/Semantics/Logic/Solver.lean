import RUXt.Model.Refute
import RUXt.Semantics.Logic.Poly
import RUXt.Semantics.Summary.Subvariant.Basic

/-!
# The semantic solver

The solver `semSolver` answering satisfiability queries by satisfiability of the instance
(`Sat`) and simplification queries by logical equivalence (`HEquiv`) at every tuple of
symbolic values.

Satisfiability of the postcondition of a summary, at a single instance (`Summary.SatAt`) and
at some tuple of types (`Summary.SatOwned`), and the answers `semSolver` gives on the
assertions `Subvariant.symAsrt` and `Subvariant.typedSymAsrt`.
-/

namespace RUXt

universe u

/-! ## Satisfiability of the postcondition of a summary -/

/-- The postcondition of a summary is satisfiable at the general arguments `args` and the
typed subvariant arguments `S`: it holds of some state, for some result value. -/
def Summary.SatAt (ς : Summary) (args : TeleArg ς.ownedTele)
    (S : SubvArgs.{0} ς.src.arity) : Prop :=
  ∃ v, Sat (ς.ownedAt v args S)

/-- The postcondition of a summary is satisfiable: it holds of some state, at some tuple of
*types* for its type parameters, some symbolic values of the source, some input values and
some result value, the type parameters being described by the bare types
(`SubvArgs.ofTys`). -/
def Summary.SatOwned (ς : Summary) : Prop :=
  ∃ (args : TeleArg ς.ownedTele) (T : TyArgs ς.src.arity), ς.SatAt args (SubvArgs.ofTys T)

/-! ## The semantic solver -/

/-- The solver answering queries by the semantics of assertions: a symbolic assertion holds
at a tuple of symbolic values when the assertion it
yields there is satisfiable, and two symbolic assertions simplify to one another when the
assertions they yield are logically equivalent at every tuple of symbolic values. -/
def semSolver : Solver where
  Model A args := Sat (A args)
  Simplify A B := ∀ args, A args ⊣⊢ B args

/-- The semantic solver accepts a symbolic assertion over the symbolic values of a small
telescope at a tuple of them exactly when the assertion it yields there is satisfiable. -/
@[simp] theorem semSolver_model_symAsrt {tt : Tele.{0}} {F : TeleArg tt → Asrt.{0}}
    {args : TeleArg (symTele tt)} :
    semSolver.Model (symAsrt F) args ↔ Sat (F args.ulower) :=
  Iff.rfl

@[simp] theorem semSolver_simplify {tt : Tele.{1}} {A B : SymAsrt.{0} tt} :
    semSolver.Simplify A B ↔ ∀ args, A args ⊣⊢ B args :=
  Iff.rfl

/-- The tuples the semantic solver accepts the postcondition of a summary at are the ones at
which it is satisfiable: a result value, symbolic values, input values and *types*, the type
parameters being described by the default subvariants of those types. -/
@[simp] theorem semSolver_model_owned_symAsrt {ς : Summary} {r : Val}
    {args : TeleArg ς.ownedTele} {T : TyArgs ς.src.arity} :
    semSolver.Model ς.owned.symAsrt
        (TeleArg.uliftArg (⟨r, args.app T⟩ :
          TeleArg ς.owned.satTele)) ↔
      Sat (ς.ownedAt r args (SubvArgs.ofTys T)) := by
  rw [Subvariant.symAsrt, semSolver_model_symAsrt, TeleArg.ulower_uliftArg]
  simp only [TeleArg.fst_append, TeleArg.snd_append]
  rfl

/-- The tuples the semantic solver accepts a subvariant at, once its type parameters are fixed,
are the symbolic values of the subvariant followed by those of the picked summaries at which it
is satisfiable for some result value and some input values: the subvariant is read at the
former, its type parameters being described at the latter; the result value and the input
values are existentially bound by the query. -/
@[simp] theorem semSolver_model_typedSymAsrt {Φ : Subvariant} {P : TypePicks}
    {args : TeleArg (symTele (Φ.typedTele P))} :
    semSolver.Model (Φ.typedSymAsrt P) args ↔
      ∃ (r : Val) (vs : TeleArg (.uniform Val Φ.valArity)),
        Sat ((Φ.asrt r).at (args.ulower.fst.app vs) (P.subvArgs Φ.arity args.ulower.snd)) := by
  rw [Subvariant.typedSymAsrt, semSolver_model_symAsrt]
  show (∃ h, HProp h (Asrt.ex _)) ↔ _
  simp only [hProp_ex, Sat]
  constructor
  · rintro ⟨h, r, vs, hh⟩
    exact ⟨r, vs, h, hh⟩
  · rintro ⟨r, vs, h, hh⟩
    exact ⟨h, r, vs, hh⟩

/-- The satisfiability check of the semantic solver on the postcondition of a summary is the
satisfiability of that postcondition. -/
@[simp] theorem semSolver_sat_owned_symAsrt {ς : Summary} :
    semSolver.Sat ς.owned.symAsrt ↔ ς.SatOwned := by
  constructor
  · rintro ⟨a, ha⟩
    rw [Subvariant.symAsrt, semSolver_model_symAsrt] at ha
    exact ⟨a.ulower.2.fst, a.ulower.2.snd, a.ulower.1, ha⟩
  · rintro ⟨args, T, r, hr⟩
    exact ⟨_, semSolver_model_owned_symAsrt.mpr hr⟩

end RUXt
