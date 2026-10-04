import RUXt.Model.Summary.Source

/-!
# Summaries and summary contexts

Subvariants (`Subvariant`), summaries (`Summary`) — a subvariant paired with the template of a
source over the same symbolic values and type parameters — and the type spaces collecting them
(`SummCtx`), starting from the base summaries (`SummCtx.base`).
-/

namespace RUXt

/-! ## Subvariants -/

/-- A subvariant: an assertion on a result value, parametric on `arity` typed subvariants, over
the symbolic values `teleOf` followed by `valArity` input values. -/
structure Subvariant : Type 1 where
  /-- The telescope of the symbolic values the subvariant depends on. -/
  teleOf : Tele.{0}
  /-- The number of input values the subvariant takes after its symbolic values. -/
  valArity : ℕ
  /-- The number of typed subvariant arguments of the subvariant. -/
  arity : ℕ
  /-- The assertion itself, as a function of the result value. -/
  asrt : Val → PolyAsrt.{0} arity (teleOf.app (.uniform Val valArity))

namespace Subvariant

/-- The general telescope of a subvariant: its symbolic values followed by its input
values. -/
abbrev genTele (Φ : Subvariant) : Tele.{0} := Φ.teleOf.app (.uniform Val Φ.valArity)

/-- The telescope of everything a subvariant depends on: the result value, its general
arguments, and one type per typed subvariant argument. -/
abbrev satTele (Φ : Subvariant) : Tele.{0} :=
  Tele.cons fun _ : Val => Φ.genTele.app (Tele.uniform Ty Φ.arity)

/-- A subvariant as a symbolic assertion of everything it depends on (`Subvariant.satTele`),
each type argument being read as the bare type (`SubvArgs.ofTys`). -/
def symAsrt (Φ : Subvariant) : SymAsrt.{0} (symTele Φ.satTele) :=
  RUXt.symAsrt fun ⟨r, args⟩ => (Φ.asrt r).at args.fst (SubvArgs.ofTys args.snd)

end Subvariant

/-! ## Summaries -/

/-- An inhabitant of a type space: its postcondition, a subvariant, and the template of its
source, over the symbolic values and type parameters of the subvariant. -/
structure Summary : Type 1 where
  /-- Owned resources, postcondition of the source function. -/
  owned : Subvariant
  /-- The template of the source function. -/
  fn : FunTempl owned.teleOf owned.arity

namespace Summary

/-- The source of a summary: its template, bundled with the shape of its postcondition. -/
abbrev src (ς : Summary) : Source := ⟨ς.owned.teleOf, ς.owned.arity, ς.fn⟩

/-- The number of input values of a summary: those of its postcondition. -/
def valArity (ς : Summary) : ℕ := ς.owned.valArity

/-- The general telescope of a summary: the symbolic values of its source, followed by its
input values. -/
def ownedTele (ς : Summary) : Tele.{0} :=
  ς.src.teleOf.app (.uniform Val ς.valArity)

/-- The assertion the postcondition of a summary gives to a result value, at general
arguments and typed subvariant arguments. -/
def ownedAt (ς : Summary) (r : Val) (args : TeleArg ς.ownedTele)
    (S : SubvArgs.{0} ς.src.arity) : Asrt.{0} :=
  (ς.owned.asrt r).at args S

/-- The summary with source `src` and postcondition `Φ`, which takes one input value per
parameter of the source. -/
def of (src : Source)
    (Φ : Val → PolyAsrt.{0} src.arity (src.teleOf.app (.uniform Val src.fn.params.length))) :
    Summary :=
  ⟨⟨src.teleOf, src.fn.params.length, src.arity, Φ⟩, src.fn⟩

end Summary

/-! ## Summary contexts -/

/-- Context under-approximating the type spaces, indexed by anonymous type constructors
(`TyConsId.anon`). -/
def SummCtx := TyConsId → List Summary
instance : EmptyCollection SummCtx := ⟨fun _ => []⟩

namespace SummCtx

/-- File the summary `ς` under the anonymous form of the type constructor `τ`. -/
def update (S : SummCtx) (τ : TyConsId) (ς : Summary) : SummCtx :=
  Function.update S τ.anon (ς :: S τ.anon)
/-- The summary `ς` is filed in `S` under the anonymous form of `τ`. -/
def MemTy (S : SummCtx) (τ : TyConsId) (ς : Summary) : Prop :=
  ς ∈ S τ.anon
/-- The summary `ς` is filed in `S` for some type constructor. -/
def Mem (S : SummCtx) (ς : Summary) : Prop :=
  ∃ τ, S.MemTy τ ς

end SummCtx

/-! ### Base summaries -/

/-- The summary of a base type: any value of that type. -/
def Summary.base : BaseTy → Summary
  | .int => Summary.of
      ⟨[tele (_ : ℤ)], 0, ⟨[], fun z => .int z, .int, true⟩⟩
      fun r z => ⌞ r = .int z.down ⌟
  | .bool => Summary.of
      ⟨[tele (_ : Bool)], 0, ⟨[], fun b => .bool b, .bool, true⟩⟩
      fun r b => ⌞ r = .bool b.down ⌟
  | .loc => Summary.of
      ⟨[tele (_ : Loc)], 0, ⟨[], fun l => .loc l, .loc, true⟩⟩
      fun r l => ⌞ r = .loc l.down ⌟
  | .unit => Summary.of
      ⟨[tele], 0, ⟨[], .unit, .unit, true⟩⟩
      fun r => ⌞ r = .unit ⌟
/-- The summary of the identity type constructor `.param 0`: the result is the input value,
owning the first subvariant of the typed subvariant supplied for the type parameter. -/
def Summary.id (Λ : Library) : Summary :=
  Summary.of
    ⟨[tele], 1, ⟨[("x", .param 0)], fun _ => .var "x", .param 0, true⟩⟩
    fun r v ts => ⌞ r = v.down ⌟ ∗ ts.get Λ 0 v.down

/-- The type space holding the base summaries and the identity summary. -/
def SummCtx.base (Λ : Library) : SummCtx :=
  (([.int, .bool, .loc, .unit] : List BaseTy).foldr
      (fun kind (S : SummCtx) => S.update (.base kind) (Summary.base kind))
      ∅).update (.param 0) (Summary.id Λ)

end RUXt
