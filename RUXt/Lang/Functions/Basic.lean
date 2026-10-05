import RUXt.Lang.Expr
import RUXt.Lang.Types.Params

namespace RUXt

/-!
# Functions: implementations and templates

A `FunImpl` is a concrete function implementation: its parameters and its result have
concrete types (`Ty`).  A `FunTempl` is the *generic* counterpart: its parameters and its
result are described by *type constructors* (`TyConsId`), and its body depends on the type
arguments and on a telescope `tt` of symbolic values.

A template carries

* a *type arity* `arity`, the number of type parameters of the template;
* a body `body`, parametric in the symbolic values of `tt` and in those `arity` types;
* the type constructors of its parameters and of its result, each of which refers to the
  type parameters of the template *directly*, by index.

The type arguments a template is concretised at are given by a *tuple* `TyArgs arity`, so
that the right number of them is supplied by construction.  Concretisation
`FunTempl.concretise` is therefore **total**: a type constructor is instantiated at the
tuple by substituting the `i`-th type of the tuple for the type parameter of index `i`
(`TyConsId.concretise`), a type parameter beyond the tuple getting the placeholder type
`Ty.unit`.  A template which never refers to such an out-of-range type parameter is
`FunTempl.Bounded`.

Where the type arguments come as a *list* — whose length is a property of the data rather than
of its type — a template is instead *instantiated* (`FunTempl.instantiate`), a partial
operation failing exactly when the list does not provide one type per type parameter.  The two
are related by `FunTempl.instantiate_toList` (instantiating at the list of a tuple is
concretising at that tuple) and `FunTempl.eq_concretise_of_instantiate` (a successful
instantiation is a concretisation).
-/

/-- A tuple of argument values for `n` parameters. -/
abbrev ValArgs (n : ℕ) : Type := TeleArg (Tele.uniform Val n)

/-- Function implementations. -/
structure FunImpl where
  params : List (PVar × Ty)
  body : Expr
  ty : Ty
  safe : Bool

namespace FunImpl

/-- The parameter names of a template. -/
def paramNames (γ : FunImpl) : List PVar :=
  γ.params.map Prod.fst

/-- Parameters of a function implementation are distinct. -/
def ParamsNodup (γ : FunImpl) : Prop := γ.paramNames.Nodup

/-- The body of an implementation with the argument values `vals` substituted for its
parameters. -/
def «with» (γ : FunImpl) {n : ℕ} (vals : ValArgs n) : Expr :=
  γ.body.substs γ.paramNames (Term.ofVals vals.toList)

end FunImpl

/-! ### Symbolic function templates -/

/-- A symbolic function template: like `FunImpl`, but with type constructors instead of
concrete types for its parameters and its result, a type arity, and a body parametric both
in the symbolic values described by the telescope `tt` and in the type arguments. -/
structure FunTempl (tt : Tele) (arity : ℕ) where
  /-- The parameters of the template, each with its type constructor. -/
  params : List (PVar × TyConsId)
  /-- The body of the template, parametric in the symbolic values of `tt` and in the
  `arity` type arguments. -/
  body : tt -t> .uniform Ty arity -t> Expr
  /-- The type constructor of the result. -/
  ty : TyConsId
  /-- Whether the template is safe. -/
  safe : Bool

namespace FunTempl

variable {tt : Tele} {arity : ℕ}

/-- The type constructors of the parameters of a template. -/
def paramCons (φ : FunTempl tt arity) : List TyConsId :=
  φ.params.map Prod.snd

/-- The number of type parameters the result type constructor of a template uses.  It may be
lower than, equal to or greater than the type arity of the template. -/
abbrev resArity (φ : FunTempl tt arity) : ℕ := φ.ty.arity

/-- The number of input values of a template: one per parameter. -/
abbrev valArity (φ : FunTempl tt arity) : ℕ := φ.params.length

/-- A template is *bounded* when every type constructor it mentions — those of its
parameters and that of its result — only refers to its own `arity` type parameters. -/
def Bounded (φ : FunTempl tt arity) : Prop :=
  (∀ p ∈ φ.params, p.2.Bounded arity) ∧ φ.ty.Bounded arity

/-- Whether a template is bounded is **decidable**: the type parameters a type constructor
uses can be read off it. -/
instance (φ : FunTempl tt arity) : Decidable φ.Bounded := by
  unfold FunTempl.Bounded; infer_instance

/-! ### The signature of a template
The *signature* of a template at a given tuple of type arguments is the list of parameter
names paired with their concrete types, together with the concrete result type.  Both are
obtained by instantiating the type constructors of the template at that tuple. -/

/-- The concrete types of the parameters, as a function of the type arguments: each
parameter type constructor is instantiated at the tuple. -/
def paramTys (φ : FunTempl tt arity) : .uniform Ty arity -t> List Ty :=
  teleBind fun types => φ.paramCons.map fun C => C.concretise types
/-- The concrete result type, as a function of the type arguments. -/
def resTy (φ : FunTempl tt arity) : .uniform Ty arity -t> Ty :=
  teleBind fun types => φ.ty.concretise types
/-- The parameter names of a template. -/
def paramNames (φ : FunTempl tt arity) : List PVar :=
  φ.params.map Prod.fst

/-- The signature of a template: its parameter names paired with their concrete types. -/
def sig (φ : FunTempl tt arity) : .uniform Ty arity -t> List (PVar × Ty) :=
  teleBind fun types => (φ.paramNames).zip (φ.paramTys.apply types)

/-! ### Concretisation

Concretising a template at symbolic values and at a *tuple* of type arguments is a total
operation: the parameters get the types provided by the signature of the template and the
result gets the instantiation of the result type constructor. -/

/-- Concretise a symbolic function template at symbolic values and a tuple of type
arguments, producing a concrete function implementation. -/
def concretise (φ : FunTempl tt arity) (vals : TeleArg tt) (types : TyArgs arity) :
    FunImpl :=
  { params := φ.sig.apply types
    body := φ.body |>.apply vals |>.apply types
    ty := φ.resTy.apply types
    safe := φ.safe }

/-! ### Instantiation at a list of type arguments

The partial counterpart of `FunTempl.concretise`: the type arguments come as a *list*, whose
length is not recorded in its type, and instantiation fails exactly when that list does not
provide one type per type parameter of the template. -/

/-- Instantiate a symbolic function template at symbolic values and a list of type
arguments.  Fails exactly when the number of type arguments does not match the type arity of
the template; otherwise it is the concretisation at the tuple of those types
(`FunTempl.instantiate_eq_some`). -/
def instantiate (φ : FunTempl tt arity) (vals : TeleArg tt) (types : List Ty) :
    Option FunImpl :=
  if types.length = arity then some (φ.concretise vals (TyArgs.ofListPad arity types))
  else none

/-! ## Properties -/

@[simp] theorem length_paramCons (φ : FunTempl tt arity) :
    φ.paramCons.length = φ.params.length := by
  simp [paramCons]

/-- The type constructor of every parameter of a bounded template only refers to the type
parameters of that template. -/
theorem Bounded.param {φ : FunTempl tt arity} (h : φ.Bounded) {p : PVar × TyConsId}
    (hp : p ∈ φ.params) : p.2.Bounded arity := h.1 p hp
/-- The result type constructor of a bounded template only refers to the type parameters of
that template. -/
theorem Bounded.res {φ : FunTempl tt arity} (h : φ.Bounded) : φ.ty.Bounded arity := h.2

@[simp] theorem paramTys_apply (φ : FunTempl tt arity) (types : TyArgs arity) :
    φ.paramTys.apply types = φ.paramCons.map fun C => C.concretise types :=
  teleBind_apply _ _
@[simp] theorem resTy_apply (φ : FunTempl tt arity) (types : TyArgs arity) :
    φ.resTy.apply types = φ.ty.concretise types :=
  teleBind_apply _ _
@[simp] theorem sig_apply (φ : FunTempl tt arity) (types : TyArgs arity) :
    φ.sig.apply types = φ.paramNames.zip (φ.paramTys.apply types) :=
  teleBind_apply _ _

/-- A template with no parameter has an empty list of parameter names. -/
@[simp] theorem paramNames_eq_nil {φ : FunTempl tt arity} (h : φ.params = []) :
    φ.paramNames = [] := by
  rw [paramNames, h, List.map_nil]
/-- A template with no parameter has an empty signature. -/
@[simp] theorem sig_apply_eq_nil {φ : FunTempl tt arity} (h : φ.params = [])
    (types : TyArgs arity) : φ.sig.apply types = [] := by
  rw [sig_apply, paramNames_eq_nil h]; rfl

/-- A template has exactly one signature entry per parameter. -/
@[simp] theorem length_sig {φ : FunTempl tt arity} {types : TyArgs arity} :
    (φ.sig.apply types).length = φ.params.length := by
  simp [paramNames]

/-- The signature of a template: every parameter, at the instantiation of its type
constructor. -/
theorem sig_apply_eq_map (φ : FunTempl tt arity) (types : TyArgs arity) :
    φ.sig.apply types = φ.params.map fun p => (p.1, p.2.concretise types) := by
  rw [sig_apply, paramTys_apply, paramNames, paramCons, List.map_map, List.zip_map']
  rfl

/-- The signature of a template keeps the parameter names of the template. -/
theorem sig_map_fst {φ : FunTempl tt arity} {types : TyArgs arity} :
    (φ.sig.apply types).map Prod.fst = φ.paramNames := by
  simp [paramNames, List.map_fst_zip]
/-- The parameter types in the signature of a template are the instantiations of its
parameter type constructors. -/
theorem sig_map_snd {φ : FunTempl tt arity} {types : TyArgs arity} :
    (φ.sig.apply types).map Prod.snd = φ.paramTys.apply types := by
  rw [sig_apply, List.map_snd_zip (by simp [paramNames])]

theorem mem_params_of_mem_sig {φ : FunTempl tt arity} {types : TyArgs arity}
    {x : PVar} {τ : Ty} (h : (x, τ) ∈ φ.sig.apply types) : x ∈ φ.paramNames := by
  rw [sig_apply] at h
  exact (List.of_mem_zip h).1

/-- Every type in the signature of a template is the instantiation of the type constructor
of one of its parameters. -/
theorem mem_paramCons_of_mem_sig {φ : FunTempl tt arity} {types : TyArgs arity}
    {x : PVar} {τ : Ty} (h : (x, τ) ∈ φ.sig.apply types) :
    ∃ C ∈ φ.paramCons, τ = C.concretise types := by
  rw [sig_apply, paramTys_apply] at h
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp (List.of_mem_zip h).2
  exact ⟨C, hC, rfl⟩

theorem concretise_params (φ : FunTempl tt arity)
    (vals : TeleArg tt) (types : TyArgs arity) :
    (φ.concretise vals types).params = φ.sig.apply types := rfl
theorem concretise_body (φ : FunTempl tt arity)
    (vals : TeleArg tt) (types : TyArgs arity) :
    (φ.concretise vals types).body = (φ.body.apply vals).apply types := rfl
theorem concretise_ty (φ : FunTempl tt arity)
    (vals : TeleArg tt) (types : TyArgs arity) :
    (φ.concretise vals types).ty = φ.resTy.apply types := rfl
theorem concretise_safe (φ : FunTempl tt arity)
    (vals : TeleArg tt) (types : TyArgs arity) :
    (φ.concretise vals types).safe = φ.safe := rfl

theorem params_concretise {φ : FunTempl tt arity}
    (vals : TeleArg tt) {types : TyArgs arity} :
    (φ.concretise vals types).paramNames = φ.paramNames := sig_map_fst
theorem length_params_concretise {φ : FunTempl tt arity}
    (vals : TeleArg tt) {types : TyArgs arity} :
    (φ.concretise vals types).params.length = φ.params.length := length_sig

/-! ### Instantiation and concretisation -/

/-- Instantiation succeeds at the right number of type arguments, with the concretisation at
the tuple of those types. -/
theorem instantiate_eq_some (φ : FunTempl tt arity) (vals : TeleArg tt) {types : List Ty}
    (h : types.length = arity) :
    φ.instantiate vals types = some (φ.concretise vals (TyArgs.ofListPad arity types)) :=
  if_pos h
/-- Instantiation fails when the number of type arguments is wrong. -/
theorem instantiate_eq_none (φ : FunTempl tt arity) (vals : TeleArg tt) {types : List Ty}
    (h : types.length ≠ arity) : φ.instantiate vals types = none :=
  if_neg h
/-- Instantiation succeeds only at the right number of type arguments. -/
theorem length_of_instantiate {φ : FunTempl tt arity} {vals : TeleArg tt}
    {types : List Ty} {γ : FunImpl} (h : φ.instantiate vals types = some γ) :
    types.length = arity := by
  by_contra hne
  rw [φ.instantiate_eq_none vals hne] at h
  cases h
/-- **Instantiating at the list of a tuple of type arguments is concretising at that
tuple.** -/
@[simp] theorem instantiate_toList (φ : FunTempl tt arity) (vals : TeleArg tt)
    (types : TyArgs arity) :
    φ.instantiate vals (TeleArg.toList types) = some (φ.concretise vals types) := by
  rw [instantiate_eq_some φ vals (TeleArg.toList_length types), TyArgs.ofListPad_toList]
/-- A successful instantiation is a concretisation at the tuple of the type arguments it is
made at. -/
theorem eq_concretise_of_instantiate {φ : FunTempl tt arity} {vals : TeleArg tt}
    {types : List Ty} {γ : FunImpl} (h : φ.instantiate vals types = some γ) :
    types.length = arity ∧ γ = φ.concretise vals (TyArgs.ofListPad arity types) := by
  have hlen := length_of_instantiate h
  rw [instantiate_eq_some φ vals hlen] at h
  exact ⟨hlen, (Option.some.inj h).symm⟩
/-- A successful instantiation is a concretisation, at *some* tuple of type arguments. -/
theorem exists_concretise_of_instantiate {φ : FunTempl tt arity} {vals : TeleArg tt}
    {types : List Ty} {γ : FunImpl} (h : φ.instantiate vals types = some γ) :
    ∃ τs : TyArgs arity, TeleArg.toList τs = types ∧ γ = φ.concretise vals τs := by
  obtain ⟨hlen, rfl⟩ := eq_concretise_of_instantiate h
  exact ⟨_, TeleArg.toList_ofListPad _ hlen, rfl⟩
/-- A template without type parameters instantiates at the empty list of type arguments, to
its concretisation at *any* tuple of (zero) type arguments. -/
theorem instantiate_nil {φ : FunTempl tt arity} (h : arity = 0) (vals : TeleArg tt)
    (types : TyArgs arity) : φ.instantiate vals [] = some (φ.concretise vals types) := by
  rw [instantiate_eq_some φ vals (h ▸ rfl)]
  exact congrArg (some ∘ φ.concretise vals) (TyArgs.ext fun i hi => absurd hi (by omega))

/-- The names of the parameters of a concretisation are parameter names of the template. -/
theorem map_fst_params_concretise_subset (φ : FunTempl tt arity)
    (vals : TeleArg tt) (types : TyArgs arity) :
    (φ.concretise vals types).paramNames ⊆ φ.paramNames := by
  intro x hx
  obtain ⟨⟨y, τy⟩, hq, rfl⟩ := List.mem_map.mp hx
  exact mem_params_of_mem_sig hq

end FunTempl

end RUXt
