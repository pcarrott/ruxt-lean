import RUXt.Semantics.Summary.Derive
import RUXt.Examples.RISL

/-!
# Deriving the postcondition of a merged call in RISL

The specification context holding the specification of a called function
(`SpecCtx.fromPicks`) and the instance of the RISL `call` rule deriving the merged call of
picked summaries (`wfSpec_mergeCall`).  The type arguments and input values of the call are
given both as well-sized tuples (`Picks.callTyArgs`, `Picks.callValArgs`) and as lists
(`Picks.callTys`, `Picks.callVals`), over the telescope of the derived triple
(`Picks.callTele`).
-/

namespace RUXt

namespace Picks

/-- The telescope of the triple derived for a call on the picked summaries: the symbolic
values and input values of the call, lifted, followed by the typed subvariants supplied for
the `arity` type parameters of the called function and for the free type parameters of the
picked summaries. -/
abbrev callTele (ςs : Picks) (arity : ℕ) : Tele.{1} :=
  polyTele (arity + ςs.freeArity) ςs.tripleTele

/-- The type arguments of the merged call, read off the telescope of the derived triple as a
*well-sized* tuple: exactly the `arity` type parameters of the called function, taken from the
types of the typed subvariants the call is made at. -/
def callTyArgs (ςs : Picks) (arity : ℕ) : TeleLift (ςs.callTele arity) (TyArgs arity) :=
  teleLift fun args => ((SubvArgs.tys args.snd).splitUniform arity ςs.freeArity).1

/-- The input values of the merged call, read off the telescope of the derived triple as a
*well-sized* tuple: exactly one value per picked summary. -/
def callValArgs (ςs : Picks) (arity : ℕ) :
    TeleLift (ςs.callTele arity) (ValArgs ςs.length) :=
  teleLift fun args =>
    TeleArg.ofListPad .unit ςs.length ((ςs.mergeVals args.snd).at args.fst.ulower)

/-- The type arguments of the merged call, as the list a call expression carries. -/
def callTys (ςs : Picks) (arity : ℕ) : TeleLift (ςs.callTele arity) (List Ty) :=
  (ςs.callTyArgs arity).toListLift

/-- The input values of the merged call, as the list a call expression carries. -/
def callVals (ςs : Picks) (arity : ℕ) : TeleLift (ςs.callTele arity) (List Val) :=
  (ςs.callValArgs arity).toListLift

@[simp] theorem callTys_at (ςs : Picks) (arity : ℕ) (args : TeleArg (ςs.callTele arity)) :
    (ςs.callTys arity).at args = (ςs.mergeTys args.snd).at args.fst.ulower := by
  rw [callTys, teleLift_at, callTyArgs, teleLift_at, mergeTys, teleLift_at, TyArgs.tyParams]

@[simp] theorem callVals_at (ςs : Picks) (arity : ℕ)
    (args : TeleArg (ςs.callTele arity)) :
    (ςs.callVals arity).at args = (ςs.mergeVals args.snd).at args.fst.ulower := by
  rw [callVals, teleLift_at, callValArgs, teleLift_at,
    TeleArg.toList_ofListPad _ (ςs.mergeVals_length args.snd args.fst.ulower)]

/-- The program of the derived triple is the merged call, written with its type and value
projections. -/
theorem mergeCall_expr (ςs : Picks) (f : Fid) {arity : ℕ} :
    ςs.mergeCall f = SymExpr.call f (ςs.callTys arity) (ςs.callVals arity) :=
  congrArg teleLift (funext fun args => by
    show Expr.call f (TyArgs.tyParams (SubvArgs.tys args.snd))
        (Term.ofVals (ςs.merge [] (fun _ r _ _ _ rs => r :: rs) args.snd args.fst.ulower)) = _
    rw [callTys_at, callVals_at, mergeTys, mergeVals, teleLift_at, teleLift_at])

end Picks

/-- The specification context holding the specification of the function being executed:
its precondition is the resources the picked summaries own, and it is called at the first
`arity` type parameters of the derived source — those of the called function — on their
results.  The specification is added to the context `Γ`. -/
abbrev SpecCtx.fromPicks (ςs : Picks) (f : Fid) (arity : ℕ) (ε : LExit)
    (Ψ : ςs.DerivedPost arity) (Γ : SpecCtx.{0} := ∅) : SpecCtx.{0} :=
  SpecCtx.update ⟨_, ςs.callTys arity, ςs.callVals arity, ςs.mergeOwned, ε, Ψ⟩ f Γ

/-- The `call` rule of RISL, applied to the merged call of the picked summaries. -/
theorem wfSpec_mergeCall {Γ : SpecCtx.{0}} (ςs : Picks) (f : Fid) (arity : ℕ)
    (ε : LExit) (Ψ : ςs.DerivedPost arity)
    (hmem : (⟨_, ςs.callTys arity, ςs.callVals arity,
      ςs.mergeOwned, ε, Ψ⟩ : FunSpec.{0}) ∈ Γ f) :
    WfSpec Γ ⟨ςs.mergeOwned, ςs.mergeCall f, ε, Ψ⟩ := by
  rw [Picks.mergeCall_expr]
  exact .call hmem

end RUXt
