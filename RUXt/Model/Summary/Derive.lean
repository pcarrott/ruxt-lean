import RUXt.Model.Summary.Basic

/-!
# Deriving a summary from a call

The summaries picked for the parameters of a call (`Picks`), the triple of the call on them
(`Picks.mergeOwned`, `Picks.mergeCall`) and its derivability in a logic (`Picks.DerivableCall`),
the source binding the picked sources in front of the call (`FunDecl.callSource`), and the
passage from the derived postcondition to a subvariant (`Picks.DerivedPost.SimplifiesTo`).
-/

namespace RUXt

/-! ## Picked summaries -/

/-- The summaries picked for the parameters of a call, each with the type constructor it is
picked for. -/
abbrev Picks := List (TyConsId × Summary)

/-- The first `arity` type arguments of a tuple of `arity + extra` type arguments. -/
def TyArgs.tyParams {arity extra : ℕ} (types : TyArgs (arity + extra)) : List Ty :=
  (types.splitUniform arity extra).1.toList

namespace Picks

/-- The type constructors the picked summaries are picked for. -/
def tyCons (ςs : Picks) : List TyConsId := ςs.map Prod.fst

/-- The sources of the picked summaries. -/
def srcs (ςs : Picks) : List Source := ςs.map fun ⟨_, ς⟩ => ς.src
/-- All symbolic values of the picked summaries. -/
def teleOf (ςs : Picks) : Tele := Source.mergedTeleOf ςs.srcs
/-- Total number of free type parameters of the picked summaries. -/
def freeArity (ςs : Picks) : ℕ := Source.mergedFreeArity ςs.srcs
/-- Total number of input values of the picked summaries. -/
def valArity : Picks → ℕ := List.foldr (fun ⟨_, ς⟩ => Nat.add ς.valArity) 0
/-- The number of picked summaries: the number of input values of the call. -/
def size : Picks → ℕ := List.length
/-- The telescope of the call on the picked summaries: their symbolic values, their input
values, and their results. -/
def tripleTele (ςs : Picks) : Tele :=
  ςs.teleOf.app (.uniform Val ςs.valArity) |>.app (.uniform Val ςs.size)

/-! ## The triple of the call -/

/-- Fold `f` over the picked summaries of a call to a function with `arity` type parameters, at
arguments `args` of the telescope of the call and typed subvariants `S` for the type parameters
of the function followed by the free ones of the picked summaries.  Each summary is given its
result value, its symbolic values, its typed subvariants and its input values. -/
def merge {X : Type _} (x : X)
    (f : (ς : Summary) → Val → TeleArg ς.src.teleOf → SubvArgs.{0} ς.src.arity →
      TeleArg (.uniform Val ς.valArity) → X → X) {arity : ℕ} :
    (ςs : Picks) → SubvArgs.{0} (arity + ςs.freeArity) → TeleArg ςs.tripleTele → X
  | [], _, _ => x
  | ⟨τ, ς⟩ :: (ςs : Picks), S, args =>
      -- Take the symbolic values of the head summary
      let syms := args.fst.fst
      -- Split off the input values of the head summary
      let ⟨rs, rets⟩ := args.fst.snd.splitUniform ς.valArity ςs.valArity
      -- Take the last result value for the head summary
      let ⟨vals, ⟨v, ⟨⟩⟩⟩ := args.snd.splitUniform ςs.size 1
      let ⟨subvs, S⟩ :=
        -- Split the typed subvariants into those of the function `T` and the free ones `F`
        let ⟨T, F⟩ := S.splitUniform arity (ς.src.freeArity + ςs.freeArity)
        -- Split off the free typed subvariants of the head summary
        let ⟨own, F⟩ := F.splitUniform ς.src.freeArity ςs.freeArity
        -- The head summary reads `T` at the type parameters of `τ`, then its free ones
        let subvs :=
          let T := T.reindex default (τ.params.getD · 0) τ.arity
          T.appendUniform own |>.reindex default id ς.src.arity
        -- The remaining summaries read `T` without the subvariants the head one consumed
        (subvs, ς.src.dropSubvArgs T τ.params |>.appendUniform F)
      -- Fold over the remaining summaries, then apply `f` to the head summary
      ςs.merge x f S (syms.snd |>.app rets |>.app vals) |> f ς v syms.fst subvs rs

/-- The precondition of the call: the separating conjunction of the postconditions of the
picked summaries, each at its own arguments. -/
def mergeOwned {arity : ℕ} (ςs : Picks) :
    PolyAsrt (arity + ςs.freeArity) ςs.tripleTele := polyAsrt fun args S =>
  (ςs.merge .emp fun ς r vs subvs rs P => ς.ownedAt r (vs.app rs) subvs ∗ P) S args

/-- The program of the call: `f` at the types of the typed subvariants of its type parameters,
on the results of the picked summaries. -/
def mergeCall {arity : ℕ} (ςs : Picks) (f : Fid) :
    PolyExpr (arity + ςs.freeArity) ςs.tripleTele := polyExpr fun args S =>
  .call f S.tys.tyParams (Term.ofVals (ςs.merge [] (fun _ r _ _ _ rs => r :: rs) S args))

/-- A postcondition of the call on the picked summaries, over the telescope of the call. -/
abbrev DerivedPost (ςs : Picks) (arity : ℕ) : Type 1 :=
  Val → PolyAsrt (arity + ςs.freeArity) ςs.tripleTele

/-- The call to `f` on the picked summaries `ςs` has the postcondition `[ε : Ψ]` in the logic
`L`: the triple from `mergeOwned` through `mergeCall` to `Ψ` is derivable. -/
def DerivableCall (ςs : Picks) (L : Logic.{0}) (Λ : Library) (f : Fid)
    {arity : ℕ} (ε : LExit) (Ψ : ςs.DerivedPost arity) : Prop :=
  L.DerivableSpec Λ ⟨ςs.mergeOwned, ςs.mergeCall f, ε, Ψ⟩

end Picks

namespace FunDecl

/-- The summaries `ςs` picked for a call to `φ` are safe in the type space `S`: each is picked
for the type constructor of the corresponding parameter of `φ`, and is filed in `S` for it. -/
def SafePicks (φ : FunDecl) (S : SummCtx) (ςs : Picks) : Prop :=
  ςs.tyCons = φ.template.paramCons ∧ ∀ p ∈ ςs, S.MemTy p.1 p.2

/-! ## The source of the derived summary -/

/-- The source of the summary derived for a call to `f`, declared by `φ`, on the picked
summaries `ςs`: the picked sources let-bound, one per parameter of `φ`, in front of the call to
`f` on those parameters.  Its symbolic values are those of the picked summaries, and its type
parameters those of `φ` followed by the free ones of the picked sources. -/
def callSource (φ : FunDecl) (f : Fid) (ςs : Picks) : Source where
  teleOf := ςs.teleOf
  arity := φ.arity + ςs.freeArity
  fn :=
    -- Bound the lengths of all names of `φ` and of the picked sources
    let m := max (maxNameLen φ.template.paramNames)
      (List.foldr (fun s => max (maxNameLen s.fn.paramNames)) 0 ςs.srcs)
    -- The parameters are those the picked sources contribute, renamed apart
    { params := boundParams m φ.template.paramCons φ.arity ςs.srcs
      -- The result type constructor is that of `φ`
      ty := φ.template.ty
      safe := .true
      body := fun args types =>
        -- Cut out the free type arguments
        let free := types.block .unit φ.arity ςs.freeArity
        -- Call `f` on the parameters of `φ`
        let call := Expr.call f (TyArgs.tyParams types) (Term.ofVars φ.template.paramNames)
        -- Let-bind the picked sources to those parameters in front of the call
        call.bindSources m types φ.template.params ςs.srcs free args }

/-! ## The subvariant of the derived summary -/

/-- The subvariants of the shape of a call to `φ` on the picked summaries `ςs`: over their
symbolic values and input values, with the type parameters of `φ` followed by the free ones of
the picked summaries. -/
abbrev Subvariant (φ : FunDecl) (ςs : Picks) : Type 1 :=
  Val → PolyAsrt.{0} (φ.arity + ςs.freeArity)
    (ςs.teleOf.app (.uniform Val ςs.valArity))

/-- A subvariant of the shape of a call, as a plain subvariant. -/
@[coe] def Subvariant.toSubvariant {φ : FunDecl} {ςs : Picks} (Ψ' : φ.Subvariant ςs) :
    RUXt.Subvariant := ⟨ςs.teleOf, ςs.valArity, φ.arity + ςs.freeArity, Ψ'⟩

set_option synthInstance.checkSynthOrder false in
/-- A subvariant of the shape of a call is implicitly a plain subvariant. -/
instance {φ : FunDecl} {ςs : Picks} : Coe (φ.Subvariant ςs) RUXt.Subvariant :=
  ⟨FunDecl.Subvariant.toSubvariant⟩

end FunDecl

/-- The subvariant `Φ` of the derived summary is obtained from the derived postcondition `Ψ`:
the solver `Θ` reports `Φ` as a simplification of `Ψ` with the input values of the call
existentially bound. -/
def Picks.DerivedPost.SimplifiesTo {φ : FunDecl} {ςs : Picks}
    (Ψ : ςs.DerivedPost φ.arity) (Θ : Solver) (Φ : φ.Subvariant ςs) : Prop :=
  Θ.Simplify
    (tt := polyTele _ (.cons fun _ : Val => ςs.teleOf.app (.uniform Val ςs.valArity)))
    (polyAsrt fun ⟨r, args⟩ S => (Φ r).at args S)
    (polyAsrt fun ⟨r, args⟩ S => .ex fun vs => (Ψ r).at (args.app vs) S)

end RUXt
