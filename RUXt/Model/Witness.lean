import RUXt.Model.Summary.Specialise

/-!
# The witness program of a refutation

A family of picks (`TypePicks`) chooses, for every type parameter of a source, a concrete type
and summaries of the type space describing it, one per parameter carrying that type parameter.

The witness program (`Source.witness`) specialises the source at every type parameter with the
picks made for it (`Source.specialiseTypes`), and runs the result at a model of the query
`Subvariant.typedSymAsrt`, in which each type parameter is described by the postconditions of
the summaries picked for it (`TypePicks.subvArgs`).
-/

namespace RUXt

/-! ## Families of picks -/

/-- A family of picks: the entry at index `i` is the type picked for the type parameter `i`,
together with the summaries describing it, the `r`-th of them for the `r`-th parameter carrying
that type parameter. -/
abbrev TypePicks := List (Ty × List Summary)

namespace TypePicks

/-- The pick made for the type parameter `i`, or the unit type with no summary beyond the
list. -/
def pick (P : TypePicks) (i : TyIdx) : Ty × List Summary :=
  P.getD i (Ty.unit, [])

/-- A family of picks is available in the type space `S` for the source `s`: there is one pick
per type parameter of `s`, with one summary per parameter of `s` carrying it, each filed in `S`
for the type picked and having no type parameter. -/
def Safe (P : TypePicks) (S : SummCtx) (s : Source) : Prop :=
  P.length = s.arity ∧ ∀ i < s.arity, (P.pick i).2.length = s.paramCount i ∧
    ∀ ς ∈ (P.pick i).2, S.MemTy (P.pick i).1.consId ς ∧ ς.src.arity = 0

/-- The symbolic values of the summaries picked for the type parameter `k`. -/
abbrev pickTele (P : TypePicks) (k : TyIdx) : Tele.{0} :=
  Source.mergedTeleOf ((P.pick k).2.map (·.src))

/-- The symbolic values of the summaries picked for the first `k` type parameters, the last
type parameter first, associated to the right. -/
def mergedTele (P : TypePicks) : ℕ → Tele.{0}
  | 0 => .nil
  | k + 1 => (P.pickTele k).app (P.mergedTele k)

/-! ## Specialising every type parameter -/

/-- The symbolic values of a source with symbolic values `t` specialised at its first `k` type
parameters: those of `t`, then those of the summaries picked for each of these type
parameters, the last one first, associated to the left. -/
def specTele (P : TypePicks) : ℕ → Tele.{0} → Tele.{0}
  | 0, t => t
  | k + 1, t => P.specTele k (t.app (P.pickTele k))

/-- The source `s` specialised at its type parameter `i` to the type picked for it, the
summaries picked for it being let-bound at the parameters carrying `i`. -/
def specStep (P : TypePicks) (m : ℕ) (i : TyIdx) (s : Source) : Source :=
  let ⟨τ, summs⟩ := P.pick i
  s.specialise m i τ.consId summs

/-- The type arity and template of `s` specialised at its first `k` type parameters, the last
one first. -/
def specFoldFn (P : TypePicks) (m : ℕ) :
    (k : ℕ) → (s : Source) → (n : ℕ) × FunTempl (P.specTele k s.teleOf) n
  | 0, s => ⟨s.arity, s.fn⟩
  | i + 1, s => P.specFoldFn m i (P.specStep m i s)

/-- The symbolic values of a source followed by those of the summaries picked for its first
`k` type parameters, reassociated into symbolic values of the specialised source. -/
def foldReindexArgs (P : TypePicks) : (k : ℕ) → (t : Tele.{0}) →
    TeleArg (t.app (P.mergedTele k)) → TeleArg (P.specTele k t)
  | 0, _, a => a.fst
  | k + 1, _, a => P.foldReindexArgs k _ a.assoc

end TypePicks

namespace Source

/-- The symbolic values of `s` followed by those of the summaries picked for its type
parameters. -/
abbrev typedTele (s : Source) (P : TypePicks) : Tele.{0} :=
  s.teleOf.app (P.mergedTele s.arity)

/-- The source `s` specialised at all of its type parameters with the picks `P`, the last one
first. -/
def specialiseTypes (s : Source) (P : TypePicks) : Source :=
  let ⟨arity, fn⟩ := P.specFoldFn (maxNameLen s.fn.paramNames) s.arity s
  ⟨P.specTele s.arity s.teleOf, arity, fn⟩

/-- The symbolic values of `s` followed by those of the picked summaries, as symbolic values of
the fully specialised source. -/
def reindexArgs (s : Source) (P : TypePicks) :
    TeleArg (s.typedTele P) → TeleArg (s.specialiseTypes P).teleOf :=
  P.foldReindexArgs s.arity s.teleOf

/-- The witness program of the source `s` at the picks `P` and the symbolic values `args`. -/
def witness (s : Source) (P : TypePicks) (args : TeleArg (s.typedTele P)) : Expr :=
  -- Specialise every type parameter of `s` with its picks
  let src := s.specialiseTypes P
  -- Reassociate the symbolic values for the specialised source
  let args := s.reindexArgs P args
  -- Instantiate the specialised source at no type argument and take its body
  match src.fn.instantiate args [] with
  | some γ => γ.body
  | none => .error

end Source

/-! ## The query at the types a family of picks describes -/

namespace TypePicks

/-- The symbolic values of the summaries picked for the type parameter `i < k`, projected out of
those of the summaries picked for the first `k` type parameters. -/
def pickArgs (P : TypePicks) :
    {k : ℕ} → TeleArg (P.mergedTele k) → (i : Fin k) → TeleArg (P.pickTele i)
  | 0, _, i => i.elim0
  | _ + 1, args, i => i.lastCases args.fst (P.pickArgs args.snd)

/-- The postconditions of summaries without type parameter, each at its own symbolic values
from `args`, as assertions on its result value. -/
def posts : (ςs : List Summary) → TeleArg (Source.mergedTeleOf (ςs.map (·.src))) →
    List (Val → Asrt.{0})
  | [], _ => []
  | ς :: ςs, args =>
    let post v :=
      let vals := .replicate ς.valArity .unit
      let types := .replicate ς.src.arity .unit
      ς.ownedAt v (args.fst.app vals) (SubvArgs.ofTys types)
    post :: posts ςs args.snd

/-- The typed subvariants the picks supply for `arity` type parameters, at the symbolic values
`args` of the picked summaries: the type picked for each type parameter, with the
postconditions of the summaries picked for it as subvariants. -/
def subvArgs (P : TypePicks) (arity : ℕ)
    (args : TeleArg (P.mergedTele arity)) : SubvArgs.{0} arity :=
  TeleArg.ofListPad default arity
    ((List.finRange arity).map fun (i : Fin arity) =>
      ⟨(P.pick i).1, posts (P.pick i).2 (P.pickArgs args i)⟩)

end TypePicks

namespace Subvariant

/-- The symbolic values of a subvariant followed by those of the summaries picked for its type
parameters. -/
def typedTele (Φ : Subvariant) (P : TypePicks) : Tele.{0} :=
  Φ.teleOf.app (P.mergedTele Φ.arity)

/-- A subvariant as a symbolic assertion of its symbolic values and those of the picked
summaries, with its type parameters described by the picks (`TypePicks.subvArgs`) and its
result value and input values existentially bound. -/
def typedSymAsrt (Φ : Subvariant) (P : TypePicks) : SymAsrt.{0} (symTele (Φ.typedTele P)) :=
  RUXt.symAsrt fun args => .ex fun r => .ex fun vs =>
    (Φ.asrt r).at (args.fst.app vs) (P.subvArgs Φ.arity args.snd)

end Subvariant

end RUXt
