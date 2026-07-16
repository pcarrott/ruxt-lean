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

/-- Types: base types or named custom types.

Custom types are parametric on another type to encode fields. For example,
the MyInt type for custom integers is defined as MyInt = .custom (.base .int) "MyInt"
and the Even type for custom even integers is defined as .custom MyInt "Even".

TODO: represent multiple fields, I will need to find a way of representing tuples. -/
inductive Ty
  | base (kind : BaseTy)
  | custom (τ : Ty) (name : Tid)
deriving DecidableEq

abbrev TyInt : Ty := .base .int
abbrev TyBool : Ty := .base .bool
abbrev TyLoc : Ty := .base .loc
abbrev TyUnit : Ty := .base .unit

/-- Custom types can be interchangeably casted to their field type. -/
def Ty.compatible : Ty → Ty → Prop
  | .base kind, .custom τ _ => compatible (.base kind) τ
  | .custom τ _, .base kind => compatible τ (.base kind)
  | τ, τ' => τ = τ'

end RUXt
