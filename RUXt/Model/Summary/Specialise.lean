import RUXt.Model.Summary.Basic

/-!
# Specialising a summary

Pinning a type parameter of a summary to a type constructor `τ`, described by supplied
summaries — one per parameter carrying the pinned type parameter, in order.  The source is
specialised by let-binding the supplied sources at those parameters (`Source.specialise`), and
the postcondition by instantiating the pinned type parameter with the typed subvariant whose
subvariants are the postconditions of the supplied summaries (`Subvariant.specialise`).

The type parameters of a specialised summary come in four blocks: those kept before the pinned
one, those of `τ`, those kept after the pinned one, and the free ones of the supplied sources.
-/

namespace RUXt

/-! ## Specialising a source -/

/-- The parameters of `s` split by pinning its type parameter `i` to `τ`: those carrying `i`,
now carrying `τ` placed at position `i` (`TyConsId.shiftTo`), and the remaining ones, with their
type constructors specialised (`TyConsId.specSubst`). -/
def Source.pinnedParams (s : Source) (i : TyIdx) (τ : TyConsId) :
    List (PVar × TyConsId) × List (PVar × TyConsId) :=
  s.fn.params.partition (fun ⟨_, τ₀⟩ => τ₀ == .param i)
    |>.map (List.map fun ⟨x, _⟩ => (x, τ.shiftTo i))
      (List.map fun ⟨x, τ₀⟩ => (x, τ₀.substCons (τ.specSubst i)))

/-- The source `s` with its type parameter `i` pinned to the type constructor `τ` (in anonymous
form), the sources of the summaries `ςs` being let-bound at the parameters carrying `i`, in
order.  Its symbolic values are those of `s` followed by those of the supplied sources. -/
def Source.specialise (m : ℕ) (s : Source)
    (i : TyIdx) (τ : TyConsId) (ςs : List Summary) : Source where
  teleOf := s.teleOf.app (mergedTeleOf srcs)
  arity := s.arity - 1 + τ.arity + mergedFreeArity srcs
  fn :=
    -- Split the parameters of `s` into the pinned and the kept ones
    let ⟨pinned, kept⟩ := s.pinnedParams i τ
    let arity := s.arity - 1 + τ.arity
    -- The parameters are the kept ones followed by those of the supplied sources
    { params := kept ++ boundParams m (.replicate ςs.length (τ.shiftTo i)) arity srcs
      -- The result type constructor is that of `s`, specialised
      ty := s.fn.ty.substCons (τ.specSubst i)
      safe := true
      body := fun args types =>
        -- Cut out the type arguments of `τ` and the free ones
        let ⟨τs, free⟩ := (types.block .unit i τ.arity, types.block .unit arity _)
        let pinnedBody :=
          let types :=
            -- The type arguments kept before the pinned one
            let before := types.block .unit 0 i
            -- The pinned type: `τ` instantiated at its type arguments
            let pinnedTy := τ.instantiate τs.toList |>.getD .unit
            -- The type arguments kept after the pinned one
            let after := types.block .unit (i + τ.arity) (s.arity - 1 - i)
            before.appendUniform (after.consUniform pinnedTy) |>.reindex .unit id s.arity
          -- Instantiate the body of `s` at the pinned type
          s.fn.body args.fst types
        -- Let-bind the supplied sources to the pinned parameters in front of it
        pinnedBody.bindSources m types pinned srcs free args.snd }
  where srcs := ςs.map (·.src)

/-! ## Specialising a subvariant -/

/-- The postconditions of the summaries `ςs`, each as an assertion on its result value, at
the shared typed subvariants `subvs` followed by its own share of the free ones `free`, its
own symbolic values from `syms` and its own input values from `vals`.  Each summary consumes
from `subvs` the subvariants of its own parameters. -/
def SubvArgs.ownAssertions {N : ℕ} (subvs : SubvArgs.{0} N) : (ςs : List Summary) →
    SubvArgs.{0} (Source.mergedFreeArity (ςs.map (·.src))) →
    TeleArg (Source.mergedTeleOf (ςs.map (·.src))) →
    TeleArg (.uniform Val (Source.mergedValArity (ςs.map (·.src)))) →
    List (Val → Asrt.{0})
  | [], _, _, _ => []
  | ς :: ςs, free, syms, vals =>
      -- Split off the free typed subvariants of the head summary
      let ⟨τs, free⟩ := free.splitUniform ς.src.freeArity _
      -- Split off the input values of the head summary
      let ⟨vs, vals⟩ := vals.splitUniform ς.src.fn.params.length _
      -- The postcondition of the head summary at its own arguments
      let own v :=
        let vals := vs.reindex .unit id ς.valArity
        let types := subvs.appendUniform τs |>.reindex default id ς.src.arity
        ς.ownedAt v (syms.fst.app vals) types
      -- The remaining summaries read `subvs` without the subvariants the head one consumed
      own :: (ς.src.dropSubvArgs subvs (List.range N)).ownAssertions ςs free syms.snd vals

/-- The input values of a source with parameters `ps` pinning its type parameter `i`: the
next value of `rs` at a parameter carrying `i`, and the next value of `vs` elsewhere. -/
def weaveVals (i : TyIdx) (vs : List Val) (rs : List Val) :
    List (PVar × TyConsId) → List Val
  | [] => []
  | p :: ps =>
    if p.2 = .param i then rs.headD .unit :: weaveVals i vs rs.tail ps
    else vs.headD .unit :: weaveVals i vs.tail rs ps

/-- The subvariant `Φ`, of a source with parameters `ps`, with its type parameter `i` pinned to
the type constructor `τ` (in anonymous form), described by the summaries `ςs`.  The values the
let-bound supplied sources produce are existentially bound. -/
def Subvariant.specialise (Φ : Subvariant) (ps : List (PVar × TyConsId))
    (i : TyIdx) (τ : TyConsId) (ςs : List Summary) : Subvariant where
  teleOf := Φ.teleOf.app (Source.mergedTeleOf (ςs.map (·.src)))
  valArity := Φ.valArity - ςs.length + Source.mergedValArity (ςs.map (·.src))
  arity := Φ.arity - 1 + τ.arity + Source.mergedFreeArity (ςs.map (·.src))
  -- Bind the values `rs` the let-bound sources produce
  asrt r := polyAsrt fun args S => .ex fun rs =>
    -- Split the input values into the kept ones and those of the supplied summaries
    let ⟨kept, vals⟩ := args.snd.splitUniform (Φ.valArity - ςs.length) _
    -- Weave `rs` into the kept input values at the pinned parameters
    let ownVals := .ofListPad .unit Φ.valArity (weaveVals i kept.toList rs ps)
    let subvs :=
      let pinnedSubv :=
        -- Cut out the typed subvariants of `τ` and the free ones
        let ⟨subvs, free⟩ : SubvArgs τ.arity × SubvArgs _ :=
          (S.block default i τ.arity, S.block default (Φ.arity - 1 + τ.arity) _)
        -- The pinned typed subvariant: `τ`, described by the postconditions of `ςs`
        ⟨τ.instantiate subvs.tys.toList |>.getD .unit,
          subvs.ownAssertions ςs free args.fst.snd vals⟩
      -- Cut out the typed subvariants kept before and after the pinned one
      let ⟨before, after⟩ :=
        (S.block default 0 i, S.block default (i + τ.arity) (Φ.arity - 1 - i))
      -- Insert the pinned typed subvariant between them
      before.appendUniform (after.consUniform pinnedSubv) |>.reindex default id Φ.arity
    -- Read `Φ` at its symbolic values, the woven input values and those typed subvariants
    (Φ.asrt r).at (args.fst.fst.app ownVals) subvs

/-! ## Specialising a summary -/

/-- The summary `ς` with its type parameter `i` pinned to the type constructor `τ`, described
by the summaries `ςs`, one per parameter of its source carrying `i`, in order. -/
def Summary.specialise (ς : Summary)
    (i : TyIdx) (τ : TyConsId) (ςs : List Summary) : Summary :=
  -- Bound the lengths of all names of `ς` and of the supplied summaries
  let m := maxNameLen (ς.src.fn.paramNames ++ ςs.flatMap fun ς => ς.src.fn.paramNames)
  -- Specialise the postcondition and the source alike
  { owned := ς.owned.specialise ς.src.fn.params i τ ςs
    fn := (ς.src.specialise m i τ ςs).fn }

end RUXt
