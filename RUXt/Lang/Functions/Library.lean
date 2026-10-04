import RUXt.Lib.PFun
import RUXt.Lang.Functions.Basic

/-!
# Function declarations and libraries

A `FunDecl` is what a library maps a function identifier to: a symbolic function template
(`FunTempl`) over the empty telescope of symbolic values, bundled with its type arity.  The
type constructors of its parameters and of its result refer to those type parameters
directly, by index, so nothing else has to be recorded about them.

The one partial operation on declarations is the *syntactic* `FunDecl.instantiate`, which
instantiates a declaration at the list of type arguments carried by a call expression: it
fails exactly when that list has the wrong length.

A `Library` maps function identifiers to declarations with valid parameters, so every
declaration it holds — and hence every implementation obtained from one — has distinct
parameter names and only refers to its own type parameters.
-/

namespace RUXt

/-! ### Function declarations

A `FunDecl` is a symbolic function template (`FunTempl`) whose telescope of symbolic values
is empty, bundled with its type arity, so that declarations with different numbers of type
parameters fit in one library.  The template is the field `template`, and the operations on
templates apply to it at the trivial tuple of symbolic values `PUnit.unit : TeleArg [tele]`. -/

/-- A function declaration: a symbolic function template over the empty telescope of
symbolic values, bundled with its type arity.  This is what a library maps a function
identifier to. -/
structure FunDecl where
  /-- The number of type parameters of the declaration. -/
  tyArity : ℕ
  /-- The underlying symbolic function template.  Its parameter and result type constructors
  refer to the `tyArity` type parameters directly, by index: the parameter of
  `fst<T₀, T₁>(p : Pair<T₀, T₁>) -> T₀` carries the type constructor
  `.custom "Pair" [.param 0, .param 1]`, and its result carries `.param 0`. -/
  template : FunTempl [tele] tyArity

instance (φ : FunDecl) : CoeDep FunDecl φ (FunTempl [tele] φ.tyArity) :=
  ⟨φ.template⟩

namespace FunDecl
/-- The tuple of type arguments of a template: exactly `tyArity` types. -/
abbrev TyArgs (φ : FunDecl) : Type := RUXt.TyArgs φ.tyArity
/-- The number of type parameters the result type constructor of a template uses.  It may be
lower than, equal to or greater than the type arity of the template. -/
abbrev resArity (φ : FunDecl) : ℕ := φ.template.ty.arity
/-- The implementation a declaration gives at a tuple of type arguments. -/
def concretise (φ : FunDecl) (tyargs : φ.TyArgs) : FunImpl :=
  φ.template.concretise PUnit.unit tyargs
/-- The number of parameters of a declaration. -/
abbrev arity (φ : FunDecl) : ℕ := φ.template.params.length
/-- The tuple of argument values a declaration is called with: exactly one value per
parameter. -/
abbrev ValArgs (φ : FunDecl) : Type := RUXt.ValArgs φ.arity
/-- The parameter names of a template. -/
def paramNames (φ : FunDecl) : List PVar :=
  φ.template.paramNames
/-- The type obtained by instantiating the result type constructor of the template at the
type arguments `tyargs`. -/
def resTy (φ : FunDecl) (tyargs : φ.TyArgs) : Ty :=
  φ.template.resTy.apply tyargs
/-- The types of the parameters, obtained by instantiating the type constructors of the
parameters at the type arguments `tyargs`.  This is the input-side counterpart of
`FunDecl.resTy`. -/
def paramTypes (φ : FunDecl) (tyargs : φ.TyArgs) : List Ty :=
  φ.template.paramTys.apply tyargs

/-- Every type constructor a declaration mentions — those of its parameters and that of its
result — only refers to its own type parameters. -/
def Bounded (φ : FunDecl) : Prop := φ.template.Bounded
instance (φ : FunDecl) : Decidable φ.Bounded := by unfold FunDecl.Bounded; infer_instance
/-- The parameter names of a template are pairwise distinct. -/
def ParamsNodup (φ : FunDecl) : Prop := φ.paramNames.Nodup
/-- The parameters of a template are valid: distinct parameter names, and type constructors
referring only to the type parameters of the template. -/
def ParamsValid (φ : FunDecl) : Prop :=
  φ.ParamsNodup ∧ φ.Bounded
/-- The type parameters of a declaration are in the order its result reads them: the result
type constructor uses the type parameters `0, …, k - 1`, in order of first occurrence
(`TyConsId.InAnonOrder`), and the remaining type parameters of the declaration, which its
result does not use, come after them.  So `f<T, U>(List<U>, Fun<U, T>) -> List<T>` is in order,
whereas `f<T, U>(List<T>, Fun<T, U>) -> List<U>` is not. -/
def TyParamsOrdered (φ : FunDecl) : Prop := φ.template.ty.InAnonOrder
instance (φ : FunDecl) : Decidable φ.TyParamsOrdered := by
  unfold FunDecl.TyParamsOrdered; infer_instance

/-- The body of a declaration, instantiated at a tuple of type arguments. -/
def bodyAt (φ : FunDecl) (tyargs : φ.TyArgs) : Expr :=
  (φ.template.body.apply PUnit.unit).apply tyargs

/-! ### Instantiation at a syntactic list of type arguments
A call expression carries a *list* of type arguments; instantiating a declaration at such a
list is the only partial operation, failing exactly when the list has the wrong length.  It is
the instantiation of the underlying template (`FunTempl.instantiate`) at the trivial tuple of
symbolic values. -/

/-- Instantiate a declaration at the list of type arguments carried by a call.  Fails exactly
when the number of type arguments does not match the type arity of the declaration. -/
def instantiate (φ : FunDecl) (τs : List Ty) : Option FunImpl :=
  φ.template.instantiate PUnit.unit τs

end FunDecl

/-! ### Libraries mapping function identifiers to their implementations -/

/-- Libraries intrinsically contain only implementations with distinct parameter
names whose bodies typecheck under the contexts formed by those parameters, and whose type
parameters are in the order their result reads them (`FunDecl.TyParamsOrdered`). -/
structure Library where
  implementations : PFun Fid FunDecl
  paramsValid : ∀ f (φ : FunDecl), implementations f = φ → φ.ParamsValid
  tyParamsOrdered : ∀ f (φ : FunDecl), implementations f = φ → φ.TyParamsOrdered

namespace Library

/-- Function `f` exists in library `Λ` with template `φ`. -/
def MapsTo (Λ : Library) (f : Fid) (φ : FunDecl) : Prop :=
  Λ.implementations f = φ
/-- The library `Λ` maps `f` to a template which, instantiated at the type arguments `τs`,
yields the implementation `γ`. -/
def Instantiates (Λ : Library) (f : Fid) (τs : List Ty) (γ : FunImpl) : Prop :=
  ∃ φ, Λ.MapsTo f φ ∧ φ.instantiate τs = some γ

end Library

/-! ## Properties -/

namespace FunDecl

@[simp] theorem concretise_body (φ : FunDecl) (tyargs : φ.TyArgs) :
    (φ.concretise tyargs).body = φ.bodyAt tyargs := rfl

@[simp] theorem concretise_params (φ : FunDecl) (tyargs : φ.TyArgs) :
    (φ.concretise tyargs).params = φ.template.sig.apply tyargs := rfl
@[simp] theorem concretise_ty (φ : FunDecl) (tyargs : φ.TyArgs) :
    (φ.concretise tyargs).ty = φ.resTy tyargs := rfl

/-- A concretisation has the parameter names of the template. -/
theorem paramNames_concretise {φ : FunDecl} {tyargs : φ.TyArgs} :
    (φ.concretise tyargs).paramNames = φ.paramNames :=
  FunTempl.sig_map_fst

/-- The parameter types of a concretisation are the instantiations of the type constructors
of the parameters of the template at the very same type arguments. -/
@[simp] theorem paramTypes_concretise (φ : FunDecl) (tyargs : φ.TyArgs) :
    (φ.concretise tyargs).params.map Prod.snd = φ.paramTypes tyargs :=
  FunTempl.sig_map_snd

/-- Instantiation succeeds at the right number of type arguments. -/
theorem instantiate_eq_some (φ : FunDecl) {τs : List Ty} (h : τs.length = φ.tyArity) :
    φ.instantiate τs = some (φ.concretise (TyArgs.ofListPad φ.tyArity τs)) :=
  φ.template.instantiate_eq_some PUnit.unit h
/-- Instantiation fails when the number of type arguments is wrong. -/
theorem instantiate_eq_none_of_arity (φ : FunDecl) (τs : List Ty)
    (h : τs.length ≠ φ.tyArity) : φ.instantiate τs = none :=
  φ.template.instantiate_eq_none PUnit.unit h
/-- Instantiation succeeds only at the right number of type arguments. -/
theorem length_of_instantiate {φ : FunDecl} {τs : List Ty} {γ : FunImpl}
    (h : φ.instantiate τs = some γ) : τs.length = φ.tyArity :=
  FunTempl.length_of_instantiate h
/-- Instantiating at the list of a tuple of type arguments is concretising at that tuple. -/
@[simp] theorem instantiate_toList (φ : FunDecl) (tyargs : φ.TyArgs) :
    φ.instantiate (TeleArg.toList tyargs) = some (φ.concretise tyargs) :=
  φ.template.instantiate_toList PUnit.unit tyargs
/-- A successful instantiation is a concretisation at the corresponding tuple of type
arguments. -/
theorem eq_concretise_of_instantiate {φ : FunDecl} {τs : List Ty} {γ : FunImpl}
    (h : φ.instantiate τs = some γ) :
    τs.length = φ.tyArity ∧ γ = φ.concretise (TyArgs.ofListPad φ.tyArity τs) :=
  FunTempl.eq_concretise_of_instantiate h
/-- A successful instantiation is a concretisation, at *some* tuple of type arguments. -/
theorem exists_concretise_of_instantiate {φ : FunDecl} {τs : List Ty} {γ : FunImpl}
    (h : φ.instantiate τs = some γ) :
    ∃ tyargs : φ.TyArgs, TeleArg.toList tyargs = τs ∧ γ = φ.concretise tyargs :=
  FunTempl.exists_concretise_of_instantiate h
/-- An instantiation has the parameter names of the template. -/
theorem params_instantiate {φ : FunDecl} {τs : List Ty} {γ : FunImpl}
    (h : φ.instantiate τs = some γ) : γ.paramNames = φ.paramNames := by
  obtain ⟨-, rfl⟩ := eq_concretise_of_instantiate h
  exact paramNames_concretise

end FunDecl

namespace Library

/-- Every template of a library has valid parameters. -/
theorem params_valid {Λ : Library} {f : Fid} {φ : FunDecl}
    (h : Λ.MapsTo f φ) : φ.ParamsValid :=
  Λ.paramsValid f φ h
/-- Parameters of every template of a library are distinct. -/
theorem params_nodup {Λ : Library} {f : Fid} {φ : FunDecl}
    (h : Λ.MapsTo f φ) : φ.paramNames.Nodup :=
  (params_valid h).1
/-- Every type constructor of every template of a library refers only to the type parameters
of that template. -/
theorem bounded {Λ : Library} {f : Fid} {φ : FunDecl}
    (h : Λ.MapsTo f φ) : φ.Bounded :=
  (params_valid h).2

theorem instance_params_nodup {Λ : Library} {f : Fid} {τs : List Ty} {γ : FunImpl}
    (h : Λ.Instantiates f τs γ) : γ.paramNames.Nodup := by
  obtain ⟨φ, hmaps, hinst⟩ := h
  rw [FunDecl.params_instantiate hinst]
  exact Λ.params_nodup hmaps

theorem instantiates_concretise {Λ : Library} {f : Fid} {φ : FunDecl}
    (h : Λ.MapsTo f φ) (τs : φ.TyArgs) : Λ.Instantiates f τs.toList (φ.concretise τs) :=
  ⟨φ, h, φ.instantiate_toList τs⟩

end Library

end RUXt
