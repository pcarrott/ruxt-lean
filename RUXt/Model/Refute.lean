import RUXt.Model.Summary.Derive
import RUXt.Model.Summary.Specialise
import RUXt.Model.Witness

/-!
# The refutation algorithm

The refutation procedure `Library.TryRefute`, the specialisation rule `SummCtx.TrySpecialise`
and the meta-loop `WfSummCtx` combining them into well-formed type spaces.  The algorithm is
parametric on the program logic `L` its calls are derived in and on the solver `Θ` answering
its satisfiability and simplification queries.
-/

namespace RUXt

/-- The refutation procedure, in the program logic `L`, with the checks on assertions
answered by the solver `Θ`.  It derives a summary of a call to a function producing `τ` on
summaries of the type space `S`; in the ok case the result is that summary, and in the error
case it is a witness program of type unsoundness. -/
def Library.TryRefute (Λ : Library) (L : Logic.{0}) (Θ : Solver) (S : SummCtx)
    (τ : TyConsId) (r : Summary ⊕ Expr) : Prop :=
  -- Pick `safe` function `f` that outputs values of type constructor `τ`
  ∃ f φ, Λ.MapsTo f φ ∧ φ.template.ty = τ ∧ φ.template.safe ∧
  -- Pick input summaries `ςs` from `S` fitting the parameters of `f`
  ∃ ςs, φ.SafePicks S ςs ∧
  -- Postcondition `[ε : Ψ]` is obtained from executing `f` on inputs `ςs`
  ∃ ε Ψ, ςs.DerivableCall L Λ f ε Ψ ∧
  -- Construct subvariant `Φ` from postcondition `Ψ`
  ∃ Φ, Ψ.SimplifiesTo Θ Φ ∧
  -- Check that the subvariant `Φ` is satisfiable
  Θ.Sat (Subvariant.symAsrt Φ) ∧
  -- Construct the source `src` of the new summary
  let src := φ.callSource f ςs
  -- Case analysis on whether the derived state is Ok
  match r with
  -- Case Ok: The result is the new summary, with postcondition `Φ` and source `src`
  | .inl ς => ε = .lok ∧ ς = ⟨Φ, src.fn⟩
  -- Cases Err/Miss: Found the source for type unsoundness
  | .inr e => ε ≠ .lok ∧
      -- For each type parameter of the source, pick a type and summary from `S`
      ∃ P, P.Safe S src ∧
      -- Extract a model `args` of the subvariant `Φ` after concretising the types with `P`
      ∃ args, Θ.Model (Subvariant.typedSymAsrt Φ P) args ∧
      -- Construct the witness `e` from the source, the picked types and the model
      e = src.witness P args.ulower

/-- The specialisation rule: the summary `ς`, filed for `τ`, is obtained by pinning a type
parameter `i` of a summary `ς₀` of the type space `S` to a type constructor `τ'`, described by
summaries of `S` filed for `τ'`, one per parameter of the source of `ς₀` carrying `i`. -/
def SummCtx.TrySpecialise (S : SummCtx) (Θ : Solver)
    (τ : TyConsId) (ς : Summary) : Prop :=
  -- Pick a summary `ς₀` of the type space
  ∃ ς₀, S.Mem ς₀ ∧
  -- Pick a type parameter `i` of the source of `ς₀`
  ∃ i, i < ς₀.src.arity ∧
  -- Pick a type constructor `τ'` to pin `i` to, together with summaries `ςs` filed for it
  ∃ τ' ςs, (∀ ς ∈ ςs, S.MemTy τ' ς) ∧
  -- Supply one summary per parameter of the source of `ς₀` carrying `i`
  ςs.length = ς₀.src.paramCount i ∧
  -- Specialise `ς₀` to `ς`, pinning `i` to the anonymous form of `τ'`
  ς = ς₀.specialise i τ'.anon ςs ∧
  -- The specialised summary is filed for the (anonymised) output type of its source
  τ = ς.fn.ty ∧
  -- Check that the specialised postcondition is still satisfiable
  Θ.Sat ς.owned.symAsrt

/-- Meta-loop for inferring valid summaries to derive well-formed contexts, the derivation
steps being taken in the program logic `L` and the checks on assertions answered by the
solver `Θ`. -/
inductive WfSummCtx (L : Logic.{0}) (Θ : Solver) (Λ : Library) : SummCtx → Prop
  | nil :
      WfSummCtx L Θ Λ (.base Λ)
  | cons {S : SummCtx} {τ : TyConsId} {ς : Summary} :
      WfSummCtx L Θ Λ S → Λ.TryRefute L Θ S τ (.inl ς) →
      WfSummCtx L Θ Λ (S.update τ ς)
  | specialise {S : SummCtx} {τ : TyConsId} {ς : Summary} :
      WfSummCtx L Θ Λ S → S.TrySpecialise Θ τ ς →
      WfSummCtx L Θ Λ (S.update τ ς)

end RUXt
