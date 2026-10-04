import RUXt.Lib.Telescopes

namespace RUXt

/-- Base types for values. -/
inductive BaseTy
  | int
  | bool
  | loc
  | unit
deriving DecidableEq

/-- Identifiers for named types. -/
abbrev Tid := String

/-- Types: base types or named custom types. -/
inductive Ty
  | base (kind : BaseTy)
  | custom (name : Tid) (τs : List Ty)
abbrev Ty.int : Ty := .base .int
abbrev Ty.bool : Ty := .base .bool
abbrev Ty.loc : Ty := .base .loc
abbrev Ty.unit : Ty := .base .unit

/-! ### Type constructors and type parameters

A *type parameter* is referred to by its **index**, a natural number.  A *type constructor*
(`TyConsId`) is a type in which some subterms are type parameters: the syntax of types extended
with the constructor `TyConsId.param i`, the type parameter of index `i`. -/

/-- The index of a type parameter: the `i`-th type parameter is `TyConsId.param i`. -/
abbrev TyIdx := ℕ

/-- A type constructor: a type whose subterms may be *type parameters*, each named by its
index.  A constructor without any parameter is a concrete type (`Ty.consId`), a bare
parameter `TyConsId.param i` is the identity constructor on the `i`-th type parameter, and
`TyConsId.custom "Pair" [.param 0, .param 1]` is `Pair<T₀, T₁>`. -/
inductive TyConsId
  | base (kind : BaseTy)
  | custom (name : Tid) (args : List TyConsId)
  | param (i : TyIdx)
abbrev TyConsId.int : TyConsId := .base .int
abbrev TyConsId.bool : TyConsId := .base .bool
abbrev TyConsId.loc : TyConsId := .base .loc
abbrev TyConsId.unit : TyConsId := .base .unit

mutual
/-- The type constructor of a concrete type: it uses no type parameter. -/
def Ty.consId : Ty → TyConsId
  | .base kind => .base kind
  | .custom name τs => .custom name (Ty.consIdList τs)
/-- The type constructors of a list of concrete types. -/
def Ty.consIdList : List Ty → List TyConsId
  | [] => []
  | τ :: τs => τ.consId :: Ty.consIdList τs
end

theorem Ty.consIdList_eq_map : ∀ τs : List Ty, Ty.consIdList τs = τs.map Ty.consId
  | [] => rfl
  | τ :: τs => by rw [Ty.consIdList, List.map_cons, Ty.consIdList_eq_map τs]

@[simp] theorem Ty.consId_base (kind : BaseTy) : (Ty.base kind).consId = .base kind := rfl
@[simp] theorem Ty.consId_custom (name : Tid) (τs : List Ty) :
    (Ty.custom name τs).consId = .custom name (τs.map Ty.consId) := by
  rw [Ty.consId, Ty.consIdList_eq_map]

/-! ### Induction and decidable equality

`TyConsId` is a *nested* inductive type (its arguments are a `List TyConsId`), so both the
induction principle following the structure of the arguments and decidable equality are
provided by hand. -/

/-- Induction on type constructors: the arguments of a custom constructor are available
through their membership in the argument list. -/
@[elab_as_elim] theorem TyConsId.ind' {P : TyConsId → Prop}
    (base : ∀ kind, P (.base kind)) (param : ∀ i, P (.param i))
    (custom : ∀ name args, (∀ a ∈ args, P a) → P (.custom name args)) : ∀ c, P c
  | .base kind => base kind
  | .param i => param i
  | .custom name args => custom name args fun a _ => TyConsId.ind' base param custom a

mutual
def TyConsId.beq : TyConsId → TyConsId → Bool
  | .base kind, .base kind' => kind == kind'
  | .param i, .param j => i == j
  | .custom name args, .custom name' args' => (name == name') && TyConsId.beqList args args'
  | _, _ => false
def TyConsId.beqList : List TyConsId → List TyConsId → Bool
  | [], [] => true
  | c :: cs, c' :: cs' => TyConsId.beq c c' && TyConsId.beqList cs cs'
  | _, _ => false
end

mutual
theorem TyConsId.beq_iff : ∀ (c c' : TyConsId), TyConsId.beq c c' = true ↔ c = c'
  | .base _, cₓ | .param _, cₓ => by cases cₓ <;> simp [TyConsId.beq]
  | .custom .., .base _ => by simp [TyConsId.beq]
  | .custom .., .param _ => by simp [TyConsId.beq]
  | .custom name args, .custom name' args' => by
      simp only [TyConsId.beq, Bool.and_eq_true, beq_iff_eq, TyConsId.custom.injEq]
      rw [TyConsId.beqList_iff args args']
theorem TyConsId.beqList_iff : ∀ (cs cs' : List TyConsId),
    TyConsId.beqList cs cs' = true ↔ cs = cs'
  | [], csₓ | csₓ, [] => by cases csₓ <;> simp [TyConsId.beqList]
  | c :: cs, c' :: cs' => by
      simp only [TyConsId.beqList, Bool.and_eq_true, List.cons.injEq]
      rw [TyConsId.beq_iff c c', TyConsId.beqList_iff cs cs']
end

instance : DecidableEq TyConsId := fun c c' => decidable_of_iff _ (TyConsId.beq_iff c c')

end RUXt
