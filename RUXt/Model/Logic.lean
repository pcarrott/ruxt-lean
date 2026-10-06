import RUXt.Lang.Typechecker
import RUXt.Lang.Semantics
import RUXt.Lib.Telescopes

/-!
# Assertions, symbolic triples, logics and solvers

The syntactic objects the refutation algorithm manipulates:

* the assertion language `Asrt` and its notations;
* symbolic assertions `SymAsrt`, symbolic programs `SymExpr` and symbolic triples `SymTriple`,
  all functions of the symbolic values bound by a telescope;
* typed subvariants (`TypedSubvariants`) and the triples parametric on them, whose assertions
  `PolyAsrt` and programs `PolyExpr` are symbolic ones over a telescope binding the typed
  subvariants after the symbolic values;
* program logics deriving triples (`Logic`) and solvers answering satisfiability and
  simplification queries (`Solver`).

Assertions are purely syntactic here: no definition of this file refers to their meaning.
-/

namespace RUXt

open scoped PFun

universe u

/-! ## Assertions -/

/-! ### Assertion language -/

/-- Assertions. Lives in `Type (u + 1)` because existentials
quantify over arbitrary smaller types in `Type u`. -/
inductive Asrt
  | pure (P : Prop)
  | true
  | false
  | and (a₁ a₂ : Asrt)
  | or (a₁ a₂ : Asrt)
  | implies (a₁ a₂ : Asrt)
  | ex {X : Type _} (P : X → Asrt)
  | emp
  | single (l : Loc) (bv : BlockValue)
  | star (a₁ a₂ : Asrt)
  | opaque (Λ : Library) (τ : Ty) (v : Val)

/-- `⌞ P ⌟`: a pure assertion over the empty heap. -/
scoped notation "⌞" P "⌟" => Asrt.pure P
/-- `⌜ P ⌝`: `P` weakened to an affine assertion, `P ∗ TRUE`. -/
scoped notation "⌜" P "⌝" => Asrt.star P Asrt.true

/-- `l ↦ v`: the heap is a single one-cell block at `l` containing `v`. -/
def Asrt.pointsTo (l : Loc) (v : Val) : Asrt :=
  .single l (.block 1 (PFun.singleton l.2 (.val v)))
@[inherit_doc] scoped infix:67 " ↦ " => Asrt.pointsTo
/-- `l ↦∅`: the heap is a single freed block at `l`. -/
def Asrt.pointsToFreed (l : Loc) : Asrt :=
  .single l .freed
@[inherit_doc] scoped postfix:67 " ↦∅" => Asrt.pointsToFreed
/-- `l ↦?`: the heap is a single uninitialised one-cell block at `l`. -/
def Asrt.pointsToUninit (l : Loc) : Asrt :=
  .single l (.block 1 (PFun.singleton l.2 .poison))
@[inherit_doc] scoped postfix:67 " ↦?" => Asrt.pointsToUninit

/-- `P ∧ₕ Q`: conjunction of assertions. -/
scoped infixr:62 " ∧ₕ " => Asrt.and
/-- `P ∨ₕ Q`: disjunction of assertions. -/
scoped infixr:61 " ∨ₕ " => Asrt.or
/-- `P →ₕ Q`: implication of assertions. -/
scoped infixr:60 " →ₕ " => Asrt.implies
/-- `P ∗ Q`: separating conjunction. -/
scoped infixr:63 " ∗ " => Asrt.star

/-- Iterated separating conjunction over a list, with access to the position of each
element. -/
def Asrt.iterI {X : Type _} (xs : List X) (P : ℕ → X → Asrt) : Asrt :=
  match xs with
  | [] => .emp
  | x :: xs => P 0 x ∗ Asrt.iterI xs (fun n => P (n + 1))
/-- `[∗ xs , P]`: iterated separating conjunction over a list. -/
def Asrt.iter {X : Type _} (xs : List X) (P : X → Asrt) : Asrt :=
  Asrt.iterI xs fun _ => P

/-- `l ↦∗ vs`: `vs` stored contiguously starting at `l`. -/
def Asrt.pointsToMany (l : Loc) (vs : List Val) : Asrt :=
  .iterI vs fun i v => (l +ₗ i) ↦ v
/-- An optionally initialised cell. -/
def optInit (l : Loc) (v : Option Val) : Asrt :=
  match v with
  | some v => l ↦ v
  | none => Asrt.pointsToUninit l
/-- `l ↦∗? vs`: optionally initialised cells stored contiguously at `l`. -/
def Asrt.pointsToManyOpt (l : Loc) (vs : List (Option Val)) : Asrt :=
  .iterI vs fun i v => optInit (l +ₗ i) v

/-! ## Symbolic triples

A symbolic triple over a telescope `tt` is a triple whose components are functions of the
symbolic values `tt` binds, i.e. of an environment `TeleArg tt`.  The telescope lives one
universe above the assertions, `tt : Tele.{u + 1}` for assertions `Asrt.{u}`, so that it may
bind typed subvariants, which store assertions.  Small binder types are lifted into that
universe (`symTele`); small *result* types such as `Expr` need no lifting, since a function
`TeleArg tt → Expr` already lives in the universe of `TeleArg tt`. -/

/-- Symbolic assertions over the telescope `tt`: assertions depending on an environment of the
symbolic values `tt` binds. -/
abbrev SymAsrt (tt : Tele.{u + 1}) : Type (u + 1) := TeleArg tt → Asrt.{u}
/-- Symbolic expressions over the telescope `tt`: expressions depending on an environment of
the symbolic values `tt` binds. -/
abbrev SymExpr (tt : Tele.{u + 1}) : Type (u + 1) := TeleArg tt → Expr

/-- The telescope of the logic binding the symbolic values of a small telescope `tt`. -/
abbrev symTele (tt : Tele.{u}) : Tele.{u + 1} := Tele.ulift.{u, u + 1} tt

/-- The symbolic assertion over the symbolic values of a small telescope given by an ordinary
function of those values. -/
def symAsrt {tt : Tele.{u}} (F : TeleArg tt → Asrt.{u}) : SymAsrt (symTele tt) :=
  fun args => F args.ulower

/-- Termination tags at the logic level. -/
inductive LExit
  | lok : LExit
  | lerr : LExit
  | lmiss : LExit
/-- Symbolic triples: a precondition, a program, an exit tag and a postcondition on the
result value, all over the same telescope of symbolic values. -/
def SymTriple (tt : Tele.{u + 1}) : Type (u + 1) :=
  SymAsrt tt × SymExpr tt × LExit × (Val → SymAsrt tt)

/-! ## Typed subvariants -/

/-- A type argument together with the subvariants of its inhabitants: assertions on a value,
read positionally, the `k`-th one describing the value at the `k`-th parameter carrying the
type parameter it is supplied for. -/
structure TypedSubvariants : Type (u + 1) where
  /-- The type itself. -/
  ty : Ty
  /-- The subvariants, in order. -/
  own : List (Val → Asrt.{u})

/-- The telescope binding `n` typed subvariants. -/
def subvArgTele (n : ℕ) : Tele.{u + 1} := .uniform TypedSubvariants.{u} n

/-- The placeholder typed subvariant: the unit type, with no subvariant. -/
instance : Inhabited TypedSubvariants.{u} := ⟨⟨Ty.unit, []⟩⟩

/-- A tuple of `n` typed subvariants. -/
abbrev SubvArgs (n : ℕ) : Type (u + 1) := TeleArg (subvArgTele.{u} n)

namespace TypedSubvariants

/-- The assertion that `v` owns the resources of the `i`-th subvariant of `ts`; beyond the
list of subvariants, the opaque predicate of the type. -/
def get (ts : TypedSubvariants.{u}) (Λ : Library) (i : ℕ) (v : Val) : Asrt.{u} :=
  match ts.own[i]? with
  | some s => s v
  | none => .opaque Λ ts.ty v

/-- The typed subvariant of a bare type: the type with no subvariant, so that every position
is read as the opaque predicate of the type. -/
def ofTy (τ : Ty) : TypedSubvariants.{u} := ⟨τ, []⟩

end TypedSubvariants

namespace SubvArgs

variable {n : ℕ}

/-- The typed subvariant at position `i`, or the placeholder beyond the tuple. -/
def get (S : SubvArgs.{u} n) (i : ℕ) : TypedSubvariants.{u} := S.toList.getD i default

/-- The types of a tuple of typed subvariants. -/
def tys (S : SubvArgs.{u} n) : TyArgs n := S.mapUniform TypedSubvariants.ty

/-- The tuple of typed subvariants of a tuple of bare types (`TypedSubvariants.ofTy`). -/
def ofTys (T : TyArgs n) : SubvArgs.{u} n := T.mapUniform TypedSubvariants.ofTy

end SubvArgs

/-! ## Triples parametric on typed subvariants

A triple parametric on `n` typed subvariants over a small telescope `tt` is a symbolic triple
over `polyTele n tt`, which binds the symbolic values of `tt` followed by `n` typed
subvariants. -/

/-- The symbolic values of `tt`, lifted into the universe of the logic, followed by `n` typed
subvariants. -/
abbrev polyTele (n : ℕ) (tt : Tele.{u}) : Tele.{u + 1} :=
  (Tele.ulift.{u, u + 1} tt).app (subvArgTele.{u} n)

/-- The assertions of a triple parametric on `n` typed subvariants over `tt`. -/
abbrev PolyAsrt (n : ℕ) (tt : Tele.{u}) : Type (u + 1) := SymAsrt (polyTele.{u} n tt)

/-- The programs of a triple parametric on `n` typed subvariants over `tt`. -/
abbrev PolyExpr (n : ℕ) (tt : Tele.{u}) : Type (u + 1) := SymExpr (polyTele.{u} n tt)

/-- The assertion a poly assertion gives at a tuple of symbolic values and a tuple of typed
subvariants. -/
def PolyAsrt.at {n : ℕ} {tt : Tele.{u}} (P : PolyAsrt n tt) (args : TeleArg tt)
    (S : SubvArgs.{u} n) : Asrt.{u} :=
  P ((TeleArg.uliftArg args).app S)

/-- The poly assertion given by an ordinary function of the symbolic values and of the typed
subvariants. -/
def polyAsrt {n : ℕ} {tt : Tele.{u}} (F : TeleArg tt → SubvArgs.{u} n → Asrt.{u}) :
    PolyAsrt n tt :=
  fun args => F args.fst.ulower args.snd

/-- The poly program given by an ordinary function of the symbolic values and of the typed
subvariants. -/
def polyExpr {n : ℕ} {tt : Tele.{u}} (e : TeleArg tt → SubvArgs.{u} n → Expr) :
    PolyExpr n tt :=
  fun args => e args.fst.ulower args.snd

/-! ## Logics and solvers -/

/-- A program logic: the triples it derives.  The universe of a logic is the universe of the
assertions of those triples. -/
structure Logic where
  /-- The specifications the logic derives. -/
  DerivableSpec {tt : Tele.{u + 1}} : Library → SymTriple.{u} tt → Prop

/-- The checks on symbolic assertions the refutation algorithm queries. -/
structure Solver where
  /-- The satisfiability check: the tuples of symbolic values at which a symbolic assertion is
  reported to hold of some state. -/
  Model {tt : Tele.{1}} : SymAsrt.{0} tt → TeleArg tt → Prop
  /-- The simplification check: the pairs of symbolic assertions over the same telescope
  reported as interchangeable. -/
  Simplify {tt : Tele.{1}} : SymAsrt.{0} tt → SymAsrt.{0} tt → Prop

/-- A symbolic assertion the solver reports as satisfiable at some tuple of symbolic
values. -/
def Solver.Sat (Θ : Solver) {tt : Tele.{1}} (P : SymAsrt.{0} tt) : Prop :=
  ∃ args, Θ.Model P args

end RUXt
