import RUXt.Model.Refute
import RUXt.Semantics.Logic.Basic

/-!
# The semantics of sources

Notions about sources and their properties: the types bound sources produce
(`Source.resTys`), the requirement on the type parameters prescribed for them
(`Source.SelsOk`), the specification of a renaming family (`RenameSpec`, met by
`PVar.freshen`), the resources input values own at the parameters of a template
(`FunTempl.ownVals`), structural validity (`FunTempl.Valid`) and typechecking
(`FunTempl.Typechecks`) of templates.

Then the template binding sources in front of an expression (`bindSourcesAux`): it is
structurally valid and its body is a well-typed program (`Expr.bindSourcesAux_spec`), and its
body, run on the resources required by its parameters, runs the bound sources one after the
other and then the expression on their results (`Source.Runs`,
`Expr.bindSourcesAux_frameStep`).
-/

namespace RUXt

namespace Source

/-- The number of type parameters the type constructor a source produces uses. -/
abbrev resArity (s : Source) : ℕ := s.fn.ty.arity

/-- The type arguments of a source bound in a template with `N` type parameters, read off the
type arguments `types` of that template along the embedding `Source.ren`. -/
def tyArgs {N : ℕ} (s : Source) (osel : List TyIdx) (base : ℕ) (types : TyArgs N) :
    TyArgs s.arity :=
  TeleArg.reindex Ty.unit (s.ren osel base) s.arity types

/-- The type constructors of the parameters of a source, embedded along `Source.ren`. -/
def renCons (s : Source) (osel : List TyIdx) (base : ℕ) : List TyConsId :=
  s.fn.paramCons.map (·.rename (s.ren osel base))

/-- The type a source bound in a template with `N` type parameters produces, as a function of
the type arguments of that template: the type constructor of the source, with its type
parameters embedded into those of the template. -/
def resTyAt {N : ℕ} (s : Source) (osel : List TyIdx) (base : ℕ) (types : TyArgs N) : Ty :=
  (s.fn.ty.rename (s.ren osel base)).concretise types

/-- The types the sources `srcs`, bound one after the other from the free position `base` on,
produce at the type arguments `types` of the template binding them. -/
def resTys {N : ℕ} : (srcs : List Source) → List (List TyIdx) → ℕ → TyArgs N → List Ty
  | [], _, _, _ => []
  | s :: srcs, osels, base, types =>
      s.fn.resTy.apply (s.tyArgs (osels.headD []) base types)
        :: resTys srcs osels.tail (base + s.freeArity) types

/-- The sources `srcs`, bound one after the other from the free position `base` on, are
prescribed usable type parameters: the type parameters each of them is identified with are
type parameters of the template already bound at that point, and there are as many of them as
the type constructor the source produces uses. -/
def SelsOk : List Source → List (List TyIdx) → ℕ → Prop
  | [], _, _ => True
  | s :: srcs, osels, base =>
      (∀ j ∈ osels.headD [], j < base) ∧ s.resArity ≤ (osels.headD []).length ∧
      SelsOk srcs osels.tail (base + s.freeArity)

/-- Two families of selections agree on the sources `srcs`, bound one after the other: for
every source, they prescribe the same type parameter for every type parameter the type
constructor it produces uses. -/
def SelsAgree : List Source → List (List TyIdx) → List (List TyIdx) → Prop
  | [], _, _ => True
  | s :: srcs, osels, osels' =>
      (∀ k < s.resArity, (osels.headD []).getD k 0 = (osels'.headD []).getD k 0) ∧
      SelsAgree srcs osels.tail osels'.tail

end Source
/-! ### Renaming functions -/

/-- Specification of a family of renamings of variables relative to a length bound `m`: the
renamings are jointly injective and never produce a name of length at most `m`. -/
structure RenameSpec (m : ℕ) (rename : ℕ → PVar → PVar) : Prop where
  /-- Distinct variables, or variables renamed at distinct indices, receive distinct new
  names. -/
  injective : ∀ {n k : ℕ} {x y : PVar}, rename n x = rename k y → n = k ∧ x = y
  /-- A renamed variable differs from every name of length at most `m`. -/
  ne_short : ∀ {n : ℕ} {x y : PVar}, y.length ≤ m → y ≠ rename n x

/-! ### The renaming `PVar.freshen` -/

private theorem replicate_sep_inj (n k : ℕ) (a b : List Char)
    (h : List.replicate n '_' ++ '.' :: a = List.replicate k '_' ++ '.' :: b) :
    n = k ∧ a = b := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [List.replicate]
  | succ n ih =>
    cases k with
    | zero => simp [List.replicate] at h
    | succ k => simpa using ih k (by simpa [List.replicate] using h)

/-- Renames variables apart from each other and from every name of length at most `m`. -/
theorem PVar.freshen_spec {m : ℕ} : RenameSpec m (PVar.freshen m) := by
  refine ⟨?injective, ?neLength⟩
  case injective =>
    intro n k x y h
    simp only [PVar.freshen, String.ofList_inj] at h
    rw [List.append_assoc, List.append_assoc] at h
    obtain ⟨h₁, h₂⟩ := replicate_sep_inj _ _ _ _ (List.append_cancel_left h)
    exact ⟨h₁, String.toList_inj.mp h₂⟩
  case neLength =>
    intro n x y h heq
    subst heq
    have : m < (x.freshen m n).length := by
      have hlen : (x.freshen m n).toList.length = (m + 1) + n + (1 + x.length) := by
        simp [PVar.freshen, String.toList_ofList]; omega
      rw [← String.length_toList, hlen]; omega
    omega

theorem le_maxNameLen {xs : List PVar}
    {x : PVar} (h : x ∈ xs) : x.length ≤ maxNameLen xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

namespace FunTempl

variable {tt : Tele} {arity : ℕ}

/-! ### Valid templates

A template is *valid* when every one of its parameters carries a bare type parameter of the
template, and its result type constructor only uses type parameters of the template. -/

/-- Structural validity of a template: every parameter carries a bare type parameter of the
template, and the result type constructor only uses type parameters of the template. -/
def Valid (φ : FunTempl tt arity) : Prop :=
  (∀ p ∈ φ.params, ∃ i < arity, p.2 = .param i) ∧ φ.ty.Bounded arity

/-- Every parameter type of a template is one of the type arguments it is instantiated at,
ruling out parameter types such as `List<U>`. -/
def ValidTyCons (φ : FunTempl tt arity) (types : TyArgs arity) : Prop :=
  ∀ x τ, (x, τ) ∈ φ.sig.apply types → τ ∈ types.toList

end FunTempl
/-! ### Typechecking templates -/

/-- A function implementation is well-typed if its body is well-typed under the
context formed by its parameters. -/
def FunImpl.Typechecks (Λ : Library) (γ : FunImpl) : Prop :=
  let 𝕍 := VarCtx.from γ.paramNames (γ.params.map Prod.snd)
  SafeProgram 𝕍 Λ γ.ty γ.body ∧ γ.safe ∧ γ.ParamsNodup

/-- A template typechecks when it is structurally valid and, at every type instantiation,
concretises to a well-typed function implementation.  Its result type constructor may use
any of its type parameters, any number of times. -/
def FunTempl.Typechecks {tt : Tele} {arity : ℕ} (φ : FunTempl tt arity) (Λ : Library) :
    Prop :=
  φ.Valid ∧ ∀ types, ∀ args, (φ.concretise args types).Typechecks Λ

/-! ### Typechecking sources -/

namespace Source

/-- A source typechecks when its template does. -/
def Typechecks (s : Source) (Λ : Library) : Prop := s.fn.Typechecks Λ

end Source

/-! ## Properties -/

namespace Source

@[simp] theorem resTys_nil {N : ℕ} (osels : List (List TyIdx)) (base : ℕ)
    (types : TyArgs N) : resTys [] osels base types = [] := rfl
theorem resTys_cons {N : ℕ} (s : Source) (srcs : List Source) (osels : List (List TyIdx))
    (base : ℕ) (types : TyArgs N) :
    resTys (s :: srcs) osels base types
      = s.fn.resTy.apply (s.tyArgs (osels.headD []) base types)
        :: resTys srcs osels.tail (base + s.freeArity) types := rfl

theorem SelsOk.osel_lt {s : Source} {srcs : List Source} {osels : List (List TyIdx)} {base : ℕ}
    (h : SelsOk (s :: srcs) osels base) : ∀ j ∈ osels.headD [], j < base := h.1
theorem SelsOk.length_le {s : Source} {srcs : List Source} {osels : List (List TyIdx)}
    {base : ℕ} (h : SelsOk (s :: srcs) osels base) :
    s.resArity ≤ (osels.headD []).length := h.2.1
theorem SelsOk.tail {s : Source} {srcs : List Source} {osels : List (List TyIdx)} {base : ℕ}
    (h : SelsOk (s :: srcs) osels base) : SelsOk srcs osels.tail (base + s.freeArity) :=
  h.2.2
/-- The embedding of the type parameters of a bound source stays within the type parameters
of the template binding it. -/
theorem ren_lt {s : Source} {osel : List TyIdx} {base N : ℕ}
    (hosel : ∀ j ∈ osel, j < base) (hlen : s.resArity ≤ osel.length)
    (hfit : base + s.freeArity ≤ N) {i : TyIdx} (hi : i < s.arity) :
    s.ren osel base i < N :=
  Nat.lt_of_lt_of_le (TyConsId.mergeRen_lt hosel hlen le_rfl hi) hfit

end Source

/-! ### Properties of renaming -/

/-- The expression `e` behind a chain of bindings rebinding each variable `x` of `xs` to
`rename x`. -/
def Expr.bindAliases (e : Expr) (rename : PVar → PVar) : List PVar → Expr :=
  List.foldr (fun x => .letIn (.named x) (.var (rename x))) e

@[simp] theorem bindAliases_cons {rename : PVar → PVar} {x : PVar} {xs : List PVar} {e : Expr} :
    e.bindAliases rename (x :: xs)
      = .letIn (.named x) (.var (rename x)) (e.bindAliases rename xs) := rfl

/-- The alias bindings for `xs` only leave the renamed variables free. -/
theorem bindAliases_closed {rename : PVar → PVar} {e : Expr} :
    ∀ (X : Set PVar) (xs : List PVar), e.Closed (X ∪ {y | y ∈ xs}) →
      (e.bindAliases rename xs).Closed (X ∪ {y | y ∈ xs.map rename}) := by
  intro X xs
  induction xs generalizing X with
  | nil => exact fun he => he.mono fun z hz => by simpa using hz
  | cons x xs ih =>
    intro he
    refine ⟨Or.inr (by simp), (ih (X ∪ {x}) (he.mono fun z hz => ?_)).mono fun z hz => ?_⟩ <;>
      simp at hz ⊢ <;> tauto

/-- Substituting a variable other than the aliased ones passes through the bindings. -/
theorem bindAliases_substTerm {rename : PVar → PVar} {x : PVar} {t : Term} {e : Expr} :
    ∀ {xs : List PVar}, x ∉ xs → (∀ y ∈ xs, x ≠ rename y) →
      (e.bindAliases rename xs).substTerm x t = (e.substTerm x t).bindAliases rename xs := by
  intro xs
  induction xs with
  | nil => intro _ _; rfl
  | cons y ys ih =>
    intro hx hfresh
    rw [List.mem_cons, not_or] at hx
    rw [bindAliases_cons, bindAliases_cons,
      ← ih hx.2 (fun z hz => hfresh z (List.mem_cons_of_mem _ hz))]
    simp [Expr.substTerm, Pure.subst, Term.subst, Ne.symm hx.1,
      Ne.symm (hfresh y List.mem_cons_self)]

namespace FunTempl

variable {tt : Tele} {arity : ℕ}

/-- A valid template is bounded: none of its type constructors refers to a type parameter it
does not have. -/
theorem Valid.bounded {φ : FunTempl tt arity} (h : φ.Valid) : φ.Bounded := by
  refine ⟨fun p hp => ?_, h.2⟩
  obtain ⟨i, hi, hp2⟩ := h.1 p hp
  rw [hp2]
  intro j hj
  rw [TyConsId.params_param, List.mem_singleton] at hj
  exact hj ▸ hi

/-- Every parameter type of a valid template is one of the type arguments it is instantiated
at. -/
theorem Valid.validTyCons {φ : FunTempl tt arity} (h : φ.Valid)
    (types : TyArgs arity) : φ.ValidTyCons types := by
  intro x τ hx
  obtain ⟨τ, hC, rfl⟩ := mem_paramCons_of_mem_sig hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC
  obtain ⟨i, hi, hp2⟩ := h.1 p hp
  rw [hp2, TyConsId.concretise_param]
  exact TyArgs.get_mem hi

end FunTempl

/-! ### The resources input values own at the parameters of a template

An input value owns resources according to the type constructor of its parameter and the rank
of that parameter: the number of preceding parameters carrying the same constructor, counted
from an offset. -/

namespace TyConsId

/-- The offsets after one more occurrence of `C`. -/
def bumpOff (off : TyConsId → ℕ) (C : TyConsId) : TyConsId → ℕ :=
  fun D => if D = C then off D + 1 else off D

/-- The offsets after every constructor of a list. -/
def offAfter (off : TyConsId → ℕ) (cs : List TyConsId) : TyConsId → ℕ :=
  fun D => off D + cs.count D

/-- Each constructor of the list paired with its rank, counted from the offsets `off`. -/
def ranksFrom (off : TyConsId → ℕ) : List TyConsId → List (TyConsId × ℕ)
  | [] => []
  | C :: cs => (C, off C) :: ranksFrom (bumpOff off C) cs

end TyConsId

namespace FunTempl

variable {tt : Tele} {arity : ℕ}

/-- The resources the `values` own at the type constructors `cs`, read through `own` at each
constructor and its rank counted from the offsets `off`. -/
def ownValsAt (own : TyConsId → ℕ → Val → Asrt.{0}) (off : TyConsId → ℕ)
    (cs : List TyConsId) (values : List Val) : Asrt.{0} :=
  .iter (values.zip (TyConsId.ranksFrom off cs)) fun p => own p.2.1 p.2.2 p.1

/-- The resources the input `values` own at the parameters of a template, read through
`own`. -/
def ownVals (φ : FunTempl tt arity) (own : TyConsId → ℕ → Val → Asrt.{0})
    (values : List Val) : Asrt.{0} :=
  ownValsAt own (fun _ => 0) φ.paramCons values

end FunTempl

namespace TyConsId

@[simp] theorem offAfter_nil (off : TyConsId → ℕ) : offAfter off [] = off := rfl

theorem offAfter_cons (off : TyConsId → ℕ) (C : TyConsId) (cs : List TyConsId) :
    offAfter off (C :: cs) = offAfter (bumpOff off C) cs := by
  funext D
  by_cases h : D = C
  · subst h; simp [offAfter, bumpOff]; omega
  · simp [offAfter, bumpOff, h, Ne.symm h]

@[simp] theorem ranksFrom_nil (off : TyConsId → ℕ) : ranksFrom off [] = [] := rfl
@[simp] theorem ranksFrom_cons (off : TyConsId → ℕ) (C : TyConsId) (cs : List TyConsId) :
    ranksFrom off (C :: cs) = (C, off C) :: ranksFrom (bumpOff off C) cs := rfl
/-- Ranking forgets nothing: the constructors themselves are recovered. -/
@[simp] theorem map_fst_ranksFrom : ∀ (off : TyConsId → ℕ) (cs : List TyConsId),
    (ranksFrom off cs).map Prod.fst = cs
  | _, [] => rfl
  | off, C :: cs => by rw [ranksFrom_cons, List.map_cons, map_fst_ranksFrom]
@[simp] theorem length_ranksFrom : ∀ (off : TyConsId → ℕ) (cs : List TyConsId),
    (ranksFrom off cs).length = cs.length
  | _, [] => rfl
  | off, C :: cs => by simp [length_ranksFrom]

/-- Only the offsets of the constructors of the list matter. -/
theorem ranksFrom_congr : ∀ {off off' : TyConsId → ℕ} (cs : List TyConsId),
    (∀ C ∈ cs, off C = off' C) → ranksFrom off cs = ranksFrom off' cs
  | _, _, [], _ => rfl
  | off, off', C :: cs, h => by
      rw [ranksFrom_cons, ranksFrom_cons, h C List.mem_cons_self,
        ranksFrom_congr (off := bumpOff off C) (off' := bumpOff off' C) cs
          fun D hD => by
            simp only [bumpOff, h D (List.mem_cons_of_mem _ hD)]]

/-- The ranks of a concatenation: the ranks of the second part are counted from the offsets
the first part leaves behind. -/
theorem ranksFrom_append : ∀ (off : TyConsId → ℕ) (cs₁ cs₂ : List TyConsId),
    ranksFrom off (cs₁ ++ cs₂)
      = ranksFrom off cs₁ ++ ranksFrom (offAfter off cs₁) cs₂
  | off, [], cs₂ => by rw [List.nil_append, ranksFrom_nil, List.nil_append, offAfter_nil]
  | off, C :: cs₁, cs₂ => by
      rw [List.cons_append, ranksFrom_cons, ranksFrom_cons, List.cons_append,
        ranksFrom_append (bumpOff off C) cs₁ cs₂, offAfter_cons]

end TyConsId

namespace FunTempl

variable {tt : Tele} {arity : ℕ}

@[simp] theorem ownValsAt_nil_values (own : TyConsId → ℕ → Val → Asrt.{0})
    (off : TyConsId → ℕ) (cs : List TyConsId) : ownValsAt own off cs [] = .emp := rfl
@[simp] theorem ownValsAt_nil_cons (own : TyConsId → ℕ → Val → Asrt.{0})
    (off : TyConsId → ℕ) (values : List Val) : ownValsAt own off [] values = .emp := by
  rw [ownValsAt, TyConsId.ranksFrom_nil, List.zip_nil_right, Asrt.iter_nil]
@[simp] theorem ownValsAt_cons (own : TyConsId → ℕ → Val → Asrt.{0}) (off : TyConsId → ℕ)
    (C : TyConsId) (cs : List TyConsId) (v : Val) (values : List Val) :
    ownValsAt own off (C :: cs) (v :: values)
      = (own C (off C) v ∗ ownValsAt own (TyConsId.bumpOff off C) cs values) := by
  rw [ownValsAt, TyConsId.ranksFrom_cons, List.zip_cons_cons, Asrt.iter_cons, ownValsAt]

/-- Two readings agreeing on the type constructors of a list require the same resources of
the values supplied at those positions. -/
theorem ownValsAt_congr {own own' : TyConsId → ℕ → Val → Asrt.{0}} (off : TyConsId → ℕ)
    (cs : List TyConsId) (values : List Val)
    (h : ∀ C ∈ cs, ∀ k v, own C k v = own' C k v) :
    ownValsAt own off cs values = ownValsAt own' off cs values := by
  induction cs generalizing values off with
  | nil => rw [ownValsAt_nil_cons, ownValsAt_nil_cons]
  | cons C cs ih =>
    cases values with
    | nil => rw [ownValsAt_nil_values, ownValsAt_nil_values]
    | cons v values =>
      rw [ownValsAt_cons, ownValsAt_cons, h C List.mem_cons_self,
        ih _ values fun C' hC' => h C' (List.mem_cons_of_mem _ hC')]

/-- Reading the resources of a list of values at *substituted* type constructors.  When the
substitution is injective on the list, the substituted constructors are ranked exactly as the
original ones, up to the offsets they start at, so the two readings agree as soon as they do
at each constructor of the list. -/
theorem ownValsAt_map_of_inj {own own' : TyConsId → ℕ → Val → Asrt.{0}} (f : TyConsId → TyConsId) :
    ∀ (cs : List TyConsId) (values : List Val) (off off' : TyConsId → ℕ),
      (∀ C ∈ cs, ∀ D ∈ cs, f C = f D → C = D) →
      (∀ C ∈ cs, off (f C) = off' C) →
      (∀ C ∈ cs, ∀ k v, own (f C) k v = own' C k v) →
      ownValsAt own off (cs.map f) values = ownValsAt own' off' cs values := by
  intro cs
  induction cs with
  | nil => intro values off off' _ _ _; rw [List.map_nil, ownValsAt_nil_cons, ownValsAt_nil_cons]
  | cons C cs ih =>
    intro values off off' hinj hoff hown
    cases values with
    | nil => rw [ownValsAt_nil_values, ownValsAt_nil_values]
    | cons v values =>
      rw [List.map_cons, ownValsAt_cons, ownValsAt_cons, hoff C List.mem_cons_self,
        hown C List.mem_cons_self]
      refine congrArg _ (ih values _ _
        (fun D hD E hE hDE =>
          hinj D (List.mem_cons_of_mem _ hD) E (List.mem_cons_of_mem _ hE) hDE)
        ?_ fun D hD => hown D (List.mem_cons_of_mem _ hD))
      intro D hD
      rw [TyConsId.bumpOff, TyConsId.bumpOff, hoff D (List.mem_cons_of_mem _ hD)]
      by_cases hDC : D = C
      · rw [if_pos (congrArg f hDC), if_pos hDC]
      · rw [if_neg (hDC ∘ hinj D (List.mem_cons_of_mem _ hD) C List.mem_cons_self), if_neg hDC]

/-- Two rankings agreeing on the type constructors of a list rank the values supplied at
those positions alike. -/
theorem ownValsAt_congr_off (own : TyConsId → ℕ → Val → Asrt.{0}) {off off' : TyConsId → ℕ}
    (cs : List TyConsId) (values : List Val) (h : ∀ C ∈ cs, off C = off' C) :
    ownValsAt own off cs values = ownValsAt own off' cs values := by
  rw [ownValsAt, ownValsAt, TyConsId.ranksFrom_congr cs h]

/-- The resources of a list of values at appended lists of type constructors: the first part
is ranked from the offsets it starts at, the second from the offsets left after the first
(`TyConsId.offAfter`). -/
theorem ownValsAt_append (own : TyConsId → ℕ → Val → Asrt.{0}) (off : TyConsId → ℕ)
    (cs₁ cs₂ : List TyConsId) (vs₁ vs₂ : List Val) (h : vs₁.length = cs₁.length) :
    ownValsAt own off (cs₁ ++ cs₂) (vs₁ ++ vs₂)
      = Asrt.iter ((vs₁.zip (TyConsId.ranksFrom off cs₁))
          ++ (vs₂.zip (TyConsId.ranksFrom (TyConsId.offAfter off cs₁) cs₂)))
          (fun p => own p.2.1 p.2.2 p.1) := by
  rw [ownValsAt, TyConsId.ranksFrom_append,
    List.zip_append (by rw [TyConsId.length_ranksFrom, h])]

/-- Two readings agreeing on the type constructors of the parameters require the same
resources. -/
theorem ownVals_congr {φ : FunTempl tt arity} {own own' : TyConsId → ℕ → Val → Asrt.{0}}
    (values : List Val) (h : ∀ C ∈ φ.paramCons, ∀ k v, own C k v = own' C k v) :
    φ.ownVals own values = φ.ownVals own' values :=
  ownValsAt_congr _ φ.paramCons values h

end FunTempl

/-! ## Binding sources in front of an expression

`bindSourcesAux` binds sources to variables in front of an arbitrary expression of the type
arguments, renaming their parameters apart with an arbitrary family `rename`.  Its symbolic
values are those of the bound sources. -/

/-- The template binding the sources `srcs` to the variables `vars` in front of the
expression `body`, the parameters of the bound sources being renamed apart by `rename`. -/
def bindSourcesAux {N : ℕ} (body : TyArgs N → Expr)
    (rename : ℕ → PVar → PVar) (vars : List PVar) (τ : TyConsId)
    (base : ℕ) (osels : List (List TyIdx)) : (srcs : List Source) →
    FunTempl (Source.mergedTeleOf srcs) N
  | [] =>
    { params := [], ty := τ, safe := .true
      body := teleBind fun ⟨⟩ => teleBind fun types => body types }
  | s :: srcs =>
    let source :=
      bindSourcesAux body rename vars.tail τ (base + s.freeArity) osels.tail srcs
    let ρ := s.ren (osels.headD []) base
    let params := s.fn.params.map fun ⟨x, τ⟩ => ⟨rename srcs.length x, τ.rename ρ⟩
    let body := teleBind fun args => teleBind fun types =>
      let e := s.fn.body |>.apply args.fst |>.apply (TeleArg.reindex Ty.unit ρ s.arity types)
        |>.bindAliases (rename srcs.length) s.fn.paramNames
      .letIn (.named (vars.headD "unreachable")) e
        (source.body |>.apply args.snd |>.apply types)
    { params := params ++ source.params, ty := source.ty, safe := .true, body := body }

namespace FunTempl

variable {tt tt' : Tele} {n : ℕ}

/-- Structural validity only depends on the parameters and the result type constructor. -/
theorem valid_congr {φ : FunTempl tt n} {ψ : FunTempl tt' n} (hp : φ.params = ψ.params)
    (hty : φ.ty = ψ.ty) : φ.Valid ↔ ψ.Valid := by
  rw [Valid, Valid, hp, hty]

/-- The signature only depends on the parameters. -/
theorem sig_congr {φ : FunTempl tt n} {ψ : FunTempl tt' n} (hp : φ.params = ψ.params)
    (types : TyArgs n) : φ.sig.apply types = ψ.sig.apply types := by
  rw [sig_apply_eq_map, sig_apply_eq_map, hp]

theorem paramNames_congr {φ : FunTempl tt n} {ψ : FunTempl tt' n} (hp : φ.params = ψ.params) :
    φ.paramNames = ψ.paramNames := by
  rw [paramNames, paramNames, hp]

theorem paramCons_congr {φ : FunTempl tt n} {ψ : FunTempl tt' n} (hp : φ.params = ψ.params) :
    φ.paramCons = ψ.paramCons := by
  rw [paramCons, paramCons, hp]

end FunTempl

namespace Expr

/-! ### Equation lemmas for the merged source -/

section BindSrcs

variable {N : ℕ} {rename : ℕ → PVar → PVar} {vars : List PVar} {body : TyArgs N → Expr}
  {rty : TyConsId} {base : ℕ} {osels : List (List TyIdx)} {s : Source} {srcs : List Source}

@[simp] theorem bindSourcesAux_nil_params :
    (bindSourcesAux body rename vars rty base osels []).params = [] := rfl
@[simp] theorem bindSourcesAux_nil_body (args : TeleArg (Source.mergedTeleOf []))
    (types : TyArgs N) :
    ((bindSourcesAux body rename vars rty base osels []).body.apply args).apply types
      = body types := by
  rw [bindSourcesAux, teleBind_apply, teleBind_apply]

/-- The parameters of a merged source: those of the first source, renamed apart and with
their type constructors embedded into the type parameters of the merged template, followed by
the parameters of the merge of the remaining ones. -/
theorem bindSourcesAux_cons_params :
    (bindSourcesAux body rename vars rty base osels (s :: srcs)).params
      = (s.fn.params.map fun p =>
          (rename srcs.length p.1, p.2.rename (s.ren (osels.headD []) base)))
        ++ (bindSourcesAux body rename vars.tail rty (base + s.freeArity) osels.tail
            srcs).params := rfl

/-- A merged template has one parameter per input value of the sources it merges. -/
theorem bindSourcesAux_params_length :
    ∀ (srcs : List Source) (vars : List PVar) (base : ℕ) (osels : List (List TyIdx)),
      (bindSourcesAux body rename vars rty base osels srcs).params.length
        = Source.mergedValArity srcs
  | [], _, _, _ => rfl
  | s :: srcs, vars, base, osels => by
      rw [bindSourcesAux_cons_params, List.length_append, List.length_map,
        bindSourcesAux_params_length srcs vars.tail (base + s.freeArity) osels.tail]
      rfl

/-- The parameter names of a merged source: the renamed parameter names of the first
source, followed by those of the merge of the remaining ones. -/
theorem bindSourcesAux_cons_paramNames :
    (bindSourcesAux body rename vars rty base osels (s :: srcs)).paramNames
      = s.fn.paramNames.map (rename srcs.length)
        ++ (bindSourcesAux body rename vars.tail rty (base + s.freeArity) osels.tail
            srcs).paramNames := by
  rw [FunTempl.paramNames, bindSourcesAux_cons_params, List.map_append, List.map_map,
    FunTempl.paramNames, List.map_map]
  rfl

/-- The type constructors of the parameters of a merged source: those of the first source,
renamed into the type parameters of the merge, followed by those of the merge of the
remaining ones. -/
theorem bindSourcesAux_cons_paramCons :
    (bindSourcesAux body rename vars rty base osels (s :: srcs)).paramCons
      = s.fn.paramCons.map (·.rename (s.ren (osels.headD []) base))
        ++ (bindSourcesAux body rename vars.tail rty (base + s.freeArity) osels.tail
            srcs).paramCons := by
  rw [FunTempl.paramCons, bindSourcesAux_cons_params, List.map_append, List.map_map,
    FunTempl.paramCons, FunTempl.paramCons, List.map_map]
  rfl

/-- The result type constructor of a merged source is that of the merge of the remaining
sources. -/
theorem bindSourcesAux_cons_ty :
    (bindSourcesAux body rename vars rty base osels (s :: srcs)).ty
      = (bindSourcesAux body rename vars.tail rty (base + s.freeArity) osels.tail srcs).ty :=
  rfl

/-- The result type constructor of a merged source is the prescribed one. -/
@[simp] theorem bindSourcesAux_ty : ∀ (srcs : List Source) (vars : List PVar) (base : ℕ)
    (osels : List (List TyIdx)),
    (bindSourcesAux body rename vars rty base osels srcs).ty = rty
  | [], _, _, _ => rfl
  | s :: srcs, vars, base, _ => bindSourcesAux_ty srcs vars.tail (base + s.freeArity) _

/-- A merged source is safe. -/
@[simp] theorem bindSourcesAux_safe : ∀ (srcs : List Source) (vars : List PVar) (base : ℕ)
    (osels : List (List TyIdx)),
    (bindSourcesAux body rename vars rty base osels srcs).safe = Bool.true
  | [], _, _, _ => rfl
  | _ :: _, _, _, _ => rfl

/-- The body of a merged source: the body of the first source, with its parameters
rebound to their renamed counterparts, is bound to the first variable, and the merge of the
remaining sources follows. -/
theorem bindSourcesAux_cons_body (args : TeleArg (Source.mergedTeleOf (s :: srcs)))
    (types : TyArgs N) :
    ((bindSourcesAux body rename vars rty base osels (s :: srcs)).body.apply args).apply types
      = Expr.letIn (.named (vars.headD "unreachable"))
          (bindAliases (s.fn.body |>.apply args.fst |>.apply
              (s.tyArgs (osels.headD []) base types))
            (rename srcs.length) s.fn.paramNames)
          (((bindSourcesAux body rename vars.tail rty (base + s.freeArity) osels.tail
            srcs).body.apply args.snd).apply types) := by
  rw [bindSourcesAux, teleBind_apply, teleBind_apply]
  rfl

/-- The parameters of a merged source — the renamed parameters of the sources it merges —
depend on nothing but those sources, the renaming and the embedding of the type
parameters. -/
theorem bindSourcesAux_params_congr {N' : ℕ} {rty' : TyConsId}
    (t : TyArgs N → Expr) (t' : TyArgs N' → Expr) :
    ∀ (srcs : List Source) (vars vars' : List PVar) (base : ℕ)
      (osels : List (List TyIdx)),
      (bindSourcesAux t rename vars rty base osels srcs).params
        = (bindSourcesAux t' rename vars' rty' base osels srcs).params := by
  intro srcs
  induction srcs with
  | nil => exact fun _ _ _ _ => rfl
  | cons s₁ srcs ih =>
    intro vars vars' base osels
    rw [bindSourcesAux_cons_params, bindSourcesAux_cons_params,
      ih vars.tail vars'.tail _ _]

/-- The parameter names of a merged source do not depend on the expression its body ends
in. -/
theorem bindSourcesAux_paramNames_tail_irrel (t t' : TyArgs N → Expr) :
    (bindSourcesAux t rename vars rty base osels srcs).paramNames
      = (bindSourcesAux t' rename vars rty base osels srcs).paramNames := by
  rw [FunTempl.paramNames, FunTempl.paramNames,
    bindSourcesAux_params_congr t t' srcs vars vars base osels]

/-- The type constructors of the parameters of a merged source do not depend on the
expression its body ends in. -/
theorem bindSourcesAux_paramCons_tail_irrel (t t' : TyArgs N → Expr) :
    (bindSourcesAux t rename vars rty base osels srcs).paramCons
      = (bindSourcesAux t' rename vars rty base osels srcs).paramCons := by
  rw [FunTempl.paramCons, FunTempl.paramCons,
    bindSourcesAux_params_congr t t' srcs vars vars base osels]

/-- The signature of a merged source: the signature of the first source with its
parameters renamed apart, followed by the signature of the merge of the remaining ones. -/
theorem bindSourcesAux_cons_sig (hsrc : s.fn.Valid) (types : TyArgs N) :
    (bindSourcesAux body rename vars rty base osels (s :: srcs)).sig.apply types
      = ((s.fn.sig.apply (s.tyArgs (osels.headD []) base types)).map
          fun p => (rename srcs.length p.1, p.2))
        ++ (bindSourcesAux body rename vars.tail rty (base + s.freeArity) osels.tail
            srcs).sig.apply types := by
  rw [FunTempl.sig_apply_eq_map, FunTempl.sig_apply_eq_map, FunTempl.sig_apply_eq_map,
    bindSourcesAux_cons_params, List.map_append, List.map_map, List.map_map]
  refine congrArg (· ++ _) (List.map_congr_left fun p hp => ?_)
  simp [Source.tyArgs, TyConsId.concretise_reindex p.2 _ types (hsrc.bounded.1 p hp)]

end BindSrcs

end Expr

namespace Source

/-- Every family of selections agrees with itself. -/
theorem SelsAgree.refl : ∀ (srcs : List Source) (osels : List (List TyIdx)),
    SelsAgree srcs osels osels
  | [], _ => trivial
  | _ :: srcs, osels => ⟨fun _ _ => rfl, SelsAgree.refl srcs osels.tail⟩

/-- Any two families of selections agree on sources whose type constructor uses no type
parameter: no selection is ever read for them. -/
theorem SelsAgree.of_resArity : ∀ (srcs : List Source) (osels osels' : List (List TyIdx)),
    (∀ s ∈ srcs, s.resArity = 0) → SelsAgree srcs osels osels'
  | [], _, _, _ => trivial
  | s :: srcs, osels, osels', h =>
    ⟨fun k hk => absurd hk (by rw [h s (by simp)]; omega),
      SelsAgree.of_resArity srcs _ _ fun s' hs' => h s' (List.mem_cons_of_mem _ hs')⟩

/-- The embedding of the type parameters of a source only reads the selection at the type
parameters the type constructor it produces uses. -/
theorem ren_congr {s : Source} {osel osel' : List TyIdx} (base : ℕ)
    (h : ∀ k < s.resArity, osel.getD k 0 = osel'.getD k 0) :
    s.ren osel base = s.ren osel' base := by
  funext i
  unfold ren TyConsId.mergeRen
  split_ifs with hi
  · exact h _ (List.idxOf_lt_length_of_mem hi)
  · rfl

end Source

namespace Expr

/-- The merged source only depends on the selections through the type parameters they
prescribe for the type parameters the type constructors of the bound sources use. -/
theorem bindSourcesAux_sels_congr {N : ℕ} (body : TyArgs N → Expr)
    (rename : ℕ → PVar → PVar) (τ : TyConsId) :
    ∀ (srcs : List Source) (vars : List PVar) (base : ℕ) (osels osels' : List (List TyIdx)),
      Source.SelsAgree srcs osels osels' →
      bindSourcesAux body rename vars τ base osels srcs
        = bindSourcesAux body rename vars τ base osels' srcs
  | [], _, _, _, _, _ => rfl
  | s :: srcs, vars, base, osels, osels', h => by
    simp only [bindSourcesAux, Source.ren_congr base h.1,
      bindSourcesAux_sels_congr body rename τ srcs vars.tail _ _ _ h.2]

end Expr

namespace Source

/-- The number of free type parameters of the sources `s :: srcs`. -/
theorem mergedFreeArity_cons (s : Source) (srcs : List Source) :
    Source.mergedFreeArity (s :: srcs) = s.freeArity + Source.mergedFreeArity srcs := rfl

namespace Typechecks

variable {s : Source} {Λ : Library}

/-- A typechecking source is structurally valid. -/
theorem src_valid (h : s.Typechecks Λ) : s.fn.Valid := h.1

/-- The type constructor a typechecking source produces only uses its type parameters. -/
theorem ty_bounded (h : s.Typechecks Λ) : s.fn.ty.Bounded s.arity := h.1.2

/-- A typechecking source produces its type constructor, with the type parameters it uses
embedded into those of the template binding it. -/
theorem resTy_apply_eq {N : ℕ} (h : s.Typechecks Λ) (osel : List TyIdx) (base : ℕ)
    (types : TyArgs N) :
    s.fn.resTy.apply (s.tyArgs osel base types) = s.resTyAt osel base types := by
  rw [FunTempl.resTy_apply, Source.tyArgs, Source.resTyAt,
    TyConsId.concretise_reindex _ _ types h.ty_bounded]

/-- The concretisations of a typechecking source typecheck. -/
theorem concretise_typechecks (h : s.Typechecks Λ) (args : TeleArg s.teleOf)
    (types : TyArgs s.arity) :
    (s.fn.concretise args types).Typechecks Λ := h.2 types args

/-- The parameter names of a typechecking source are pairwise distinct, as soon as the
symbolic values it depends on can be supplied. -/
theorem paramNames_nodup (h : s.Typechecks Λ) (args : TeleArg s.teleOf) :
    s.fn.paramNames.Nodup := by
  obtain ⟨-, -, hdup⟩ := h.concretise_typechecks args (TeleArg.replicate _ Ty.unit)
  rwa [FunImpl.ParamsNodup, FunTempl.params_concretise _] at hdup

/-- The body of a typechecking source only uses the parameters of that source. -/
theorem body_closed (h : s.Typechecks Λ) (args : TeleArg s.teleOf)
    (types : TyArgs s.arity) :
    ((s.fn.body.apply args).apply types).Closed {y | y ∈ s.fn.paramNames} := by
  obtain ⟨hbody, -⟩ := h.concretise_typechecks args types
  refine Expr.Closed.mono (safeProgram_closed hbody) ?_
  refine subset_trans VarCtx.from_dom_subset ?_
  exact fun x hx => FunTempl.map_fst_params_concretise_subset _ _ _ hx

end Typechecks

end Source

/-! # Correctness of binding sources

For sources satisfying `Source.Ok`: the binding template is structurally valid and its body is
a well-typed program (`Expr.bindSourcesAux_spec`), and its body, run on the resources required
by its parameters, runs the bound sources one after the other and then the expression on their
results (`Source.Runs`, `Expr.bindSourcesAux_frameStep`).
-/

/-! ## Definitions -/

open scoped PFun

namespace Source

/-- The requirements the source construction places on each of the sources it binds: the
source typechecks and its parameter names are pairwise distinct. -/
structure Ok (s : Source) (Λ : Library) : Prop where
  /-- The source typechecks. -/
  typechecks : s.Typechecks Λ
  /-- The parameter names of the source are pairwise distinct. -/
  paramNames_nodup : s.fn.paramNames.Nodup

/-- `Runs Λ own off types srcs osels base args values rs g h`: the sources of `srcs`, each of
them run on exactly the resources its input values are required to own — read through `own`
off the type constructors of its parameters, transported into the type parameters of the
merge and ranked among the parameters of the merge, from the offsets `off` — produce one
after the other the results `rs`, turning the disjoint pieces of the pre-heap `g` into the
disjoint pieces of the post-heap `h`.  The parameters of a source are ranked after those of
the sources before it. -/
def Runs (Λ : Library) {N : ℕ} (own : TyConsId → ℕ → Val → Asrt.{0}) (types : TyArgs N) :
    (srcs : List Source) →
    (TyConsId → ℕ) →
    List (List TyIdx) → ℕ →
    TeleArg (Source.mergedTeleOf srcs) →
    TeleArg (Tele.uniform Val (Source.mergedValArity srcs)) →
    List Val → Heap → Heap → Prop
  | [], _, _, _, _, _, rs, g, h => rs = [] ∧ g = ∅ ∧ h = ∅
  | s :: (srcs : List Source), off, osels, base, args, values, rs, g, h =>
    ∃ (r : Val) (rs' : List Val) (g₁ g₂ h₁ h₂ : Heap),
      rs = r :: rs' ∧ g = g₁ ∪ g₂ ∧ h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂
      ∧ HProp g₁ (FunTempl.ownValsAt own off (s.renCons (osels.headD []) base)
          (values.splitUniform s.fn.params.length
            (Source.mergedValArity srcs)).1.toList)
      ∧ (Λ ⊢ ⟨g₁ | ((s.fn.body.apply args.fst).apply
            (s.tyArgs (osels.headD []) base types)).substs
              s.fn.paramNames
              (Term.ofVals (values.splitUniform s.fn.params.length
                (Source.mergedValArity srcs)).1.toList)⟩
          ⇓ᵢ ⟨h₁ | .ok r⟩)
      ∧ Runs Λ own types srcs
          (TyConsId.offAfter off (s.renCons (osels.headD []) base))
          osels.tail (base + s.freeArity) args.snd
          (values.splitUniform s.fn.params.length (Source.mergedValArity srcs)).2 rs' g₂ h₂

end Source

namespace Expr

/-- The type parameters prescribed for the sources bound in front of a call to `φ`: the type
parameters of the type constructor of the corresponding parameter of `φ`. -/
abbrev callSels (φ : FunDecl) : List (List TyIdx) :=
  φ.template.paramCons.map TyConsId.params

end Expr

/-! ## Properties

### Alias bindings -/

/-- The alias bindings introduced for the renamed source parameters typecheck, provided the
renamed variables have the expected types in the ambient context. -/
theorem bindAliases_safeProgram {Λ : Library} {m n : ℕ} {rename : ℕ → PVar → PVar}
    {ps : List (PVar × Ty)} {ν : VarCtx} {e : Expr} {τ : Ty}
    (hren : RenameSpec m rename)
    (hlen : ∀ x ∈ ps.map Prod.fst, x.length ≤ m)
    (hfresh : ∀ x τx, (x, τx) ∈ ps → ν (rename n x) = Part.some τx)
    (hbody : SafeProgram (ν.extend (ps.map Prod.fst) (ps.map Prod.snd)) Λ τ e) :
    SafeProgram ν Λ τ (e.bindAliases (rename n) (ps.map Prod.fst)) := by
  induction ps generalizing ν with
  | nil => exact hbody
  | cons p ps ih =>
    obtain ⟨x, τx⟩ := p
    rw [List.map_cons, bindAliases_cons]
    refine ⟨τx, ⟨τx, hfresh x τx (by simp), rfl⟩, ?_⟩
    refine ih (fun y hy => hlen y (by simp [hy])) (fun y τy hy => ?_) ?_
    · show PFun.insert x τx ν (rename n y) = Part.some τy
      rw [PFun.insert_apply_ne _ _ (Ne.symm (hren.ne_short (hlen x (by simp))))]
      exact hfresh y τy (List.mem_cons_of_mem _ hy)
    · rw [List.map_cons, List.map_cons, VarCtx.extend_cons] at hbody
      exact hbody

/-- Running the alias bindings on values substituted for the renamed variables has the
same behaviour as running the body with the values substituted directly. -/
theorem bindAliases_frameStep {Λ : Library} {m n : ℕ} {rename : ℕ → PVar → PVar}
    (hren : RenameSpec m rename) :
    ∀ (xs : List PVar) (vs : List Val) (e : Expr) (Z : Set PVar) (h h' : Heap) (ε : Exit),
      xs.Nodup → xs.length = vs.length → (∀ y ∈ xs, y.length ≤ m) →
      (∀ z ∈ Z, z.length ≤ m) → e.Closed (Z ∪ {y | y ∈ xs}) →
      (Λ ⊢ ⟨h | e.substs xs (Term.ofVals vs)⟩ ⇓ᵢ ⟨h' | ε⟩) →
      Λ ⊢ ⟨h | (e.bindAliases (rename n) xs).substs (xs.map (rename n)) (Term.ofVals vs)⟩
        ⇓ᵢ ⟨h' | ε⟩ := by
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ hstep; exact hstep
  | cons x xs ih =>
    intro vs e Z h h' ε hdup hlen hxlen hZ hclosed hstep
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
    obtain ⟨hxnin, hdup'⟩ := List.nodup_cons.mp hdup
    have hxfresh : x ≠ rename n x := fun heq => hren.ne_short (hxlen x (by simp)) heq
    have hfreshnin : rename n x ∉ xs.map (rename n) := by
      intro hmem
      obtain ⟨w, hw, heq⟩ := List.mem_map.mp hmem
      obtain ⟨-, rfl⟩ := hren.injective heq.symm
      exact hxnin hw
    -- the tail of the alias chain is closed and unaffected by the outer substitution
    have hclosed' : e.Closed ((Z ∪ {x}) ∪ {y | y ∈ xs}) :=
      hclosed.mono fun z hz => by simp at hz ⊢; tauto
    have htailclosed := bindAliases_closed (rename := rename n) (Z ∪ {x}) xs hclosed'
    have hxninfresh : x ∉ xs.map (rename n) := by
      intro hmem
      obtain ⟨w, -, heq⟩ := List.mem_map.mp hmem
      exact hren.ne_short (hxlen x (by simp)) heq.symm
    have hnotmem : rename n x ∉ (Z ∪ {x}) ∪ {y | y ∈ xs.map (rename n)} := by
      rintro ((hz | hz) | hz)
      · exact hren.ne_short (hZ _ hz) rfl
      · exact hxfresh hz.symm
      · exact hfreshnin hz
    have hsubst : (Expr.letIn (.named x) (.pure (.var (rename n x)))
          (e.bindAliases (rename n) xs)).substTerm (rename n x) (.val v)
        = Expr.letIn (.named x) (.pure (.val v)) (e.bindAliases (rename n) xs) := by
      simp [Expr.substTerm, Pure.subst, Term.subst, hxfresh,
        Expr.Closed.subst_eq (.val v) htailclosed hnotmem]
    rw [bindAliases_cons, List.map_cons, Term.ofVals_cons, Expr.substs_cons, hsubst,
      Expr.substs_letIn (by simpa using hlen) hxninfresh (by trivial)]
    refine FrameStep.letIn (FrameStep.pure rfl) ?_
    show FrameStep Λ h (Expr.substTerm _ x (.val v)) h' ε
    rw [Expr.substTerm_substs_comm hxninfresh,
      bindAliases_substTerm hxnin (fun y hy => fun heq => hren.ne_short (hxlen x (by simp)) heq)]
    refine ih vs (e.substTerm x (.val v)) (Z ∪ {x}) h h' ε hdup' (by simpa using hlen)
      (fun y hy => hxlen y (List.mem_cons_of_mem _ hy))
      (fun z hz => hz.elim (hZ z) fun hz => hz ▸ hxlen x (by simp))
      (Expr.Closed.subst_val x v hclosed') ?_
    simpa using hstep

namespace Source

variable {s : Source} {Λ : Library}

/-- A typechecking source is acceptable: its parameter names are automatically distinct, as
soon as the symbolic values it depends on can be supplied. -/
theorem Typechecks.ok (h : s.Typechecks Λ) (args : TeleArg s.teleOf) : s.Ok Λ :=
  ⟨h, h.paramNames_nodup args⟩

namespace Ok

/-- An acceptable source is structurally valid. -/
theorem src_valid (h : s.Ok Λ) : s.fn.Valid := h.typechecks.src_valid

/-- An acceptable source produces its type constructor, with the type parameters it uses
embedded into those of the template binding it. -/
theorem resTy_apply_eq {N : ℕ} (h : s.Ok Λ) (osel : List TyIdx) (base : ℕ) (types : TyArgs N) :
    s.fn.resTy.apply (s.tyArgs osel base types) = s.resTyAt osel base types :=
  h.typechecks.resTy_apply_eq osel base types

/-- The concretisations of an acceptable source typecheck. -/
theorem concretise_typechecks (h : s.Ok Λ) (args : TeleArg s.teleOf)
    (types : TyArgs s.arity) :
    (s.fn.concretise args types).Typechecks Λ := h.typechecks.concretise_typechecks args types

/-- The body of an acceptable source only uses the parameters of that source. -/
theorem body_closed (h : s.Ok Λ) (args : TeleArg s.teleOf) (types : TyArgs s.arity) :
    ((s.fn.body.apply args).apply types).Closed {y | y ∈ s.fn.paramNames} :=
  h.typechecks.body_closed args types

end Ok

@[simp] theorem length_renCons (s : Source) (osel : List TyIdx) (base : ℕ) :
    (s.renCons osel base).length = s.fn.params.length := by
  rw [renCons, List.length_map, FunTempl.length_paramCons]

/-- No source runs at all: no result and no resources. -/
theorem runs_nil {Λ : Library} {N : ℕ} {own : TyConsId → ℕ → Val → Asrt.{0}} {types : TyArgs N}
    {off : TyConsId → ℕ} {osels : List (List TyIdx)}
    {base : ℕ} {args : TeleArg (Source.mergedTeleOf [])}
    {values : TeleArg (Tele.uniform Val (Source.mergedValArity []))}
    {rs : List Val} {g h : Heap} :
    Runs Λ own types [] off osels base args values rs g h ↔ rs = [] ∧ g = ∅ ∧ h = ∅ := Iff.rfl

/-- The first source runs on the first group of input values, and the remaining ones run on
the rest. -/
theorem runs_cons {Λ : Library} {N : ℕ} {own : TyConsId → ℕ → Val → Asrt.{0}} {types : TyArgs N}
    {s : Source} {srcs : List Source}
    {off : TyConsId → ℕ} {osels : List (List TyIdx)} {base : ℕ}
    {args : TeleArg (Source.mergedTeleOf (s :: srcs))}
    {values : TeleArg (Tele.uniform Val (Source.mergedValArity (s :: srcs)))}
    {rs : List Val} {g h : Heap} :
    Runs Λ own types (s :: srcs) off osels base args values rs g h ↔
      ∃ (r : Val) (rs' : List Val) (g₁ g₂ h₁ h₂ : Heap),
        rs = r :: rs' ∧ g = g₁ ∪ g₂ ∧ h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂
        ∧ HProp g₁ (FunTempl.ownValsAt own off (s.renCons (osels.headD []) base)
            (values.splitUniform s.fn.params.length
              (Source.mergedValArity srcs)).1.toList)
        ∧ (Λ ⊢ ⟨g₁ | ((s.fn.body.apply args.fst).apply
              (s.tyArgs (osels.headD []) base types)).substs
                s.fn.paramNames
                (Term.ofVals (values.splitUniform s.fn.params.length
                  (Source.mergedValArity srcs)).1.toList)⟩
            ⇓ᵢ ⟨h₁ | .ok r⟩)
        ∧ Runs Λ own types srcs
            (TyConsId.offAfter off (s.renCons (osels.headD []) base))
            osels.tail (base + s.freeArity) args.snd
            (values.splitUniform s.fn.params.length (Source.mergedValArity srcs)).2 rs' g₂ h₂ :=
  Iff.rfl

/-- Running the sources produces one result per source. -/
theorem runs_length {Λ : Library} {N : ℕ} {own : TyConsId → ℕ → Val → Asrt.{0}}
    {types : TyArgs N} :
    ∀ (srcs : List Source) (off : TyConsId → ℕ) (osels : List (List TyIdx)) (base : ℕ)
      (args : TeleArg (Source.mergedTeleOf srcs))
      (values : TeleArg (Tele.uniform Val (Source.mergedValArity srcs)))
      (rs : List Val) (g h : Heap),
      Runs Λ own types srcs off osels base args values rs g h → rs.length = srcs.length := by
  intro srcs
  induction srcs with
  | nil => rintro _ _ _ _ _ rs _ _ ⟨rfl, -, -⟩; rfl
  | cons s srcs ih =>
    rintro off osels base args values rs g h
      ⟨r, rs', g₁, g₂, h₁, h₂, rfl, -, -, -, -, -, htail⟩
    rw [List.length_cons, List.length_cons, ih _ _ _ _ _ _ _ _ htail]

/-- Running the sources only depends on the tuple of type arguments, not on the arity it is
indexed by. -/
theorem runs_transport {Λ : Library} {M M' : ℕ} {own : TyConsId → ℕ → Val → Asrt.{0}}
    (hM : M = M') (types : TyArgs M)
    {srcs : List Source} {off : TyConsId → ℕ} {osels : List (List TyIdx)} {base : ℕ}
    {args : TeleArg (Source.mergedTeleOf srcs)}
    {values : TeleArg (Tele.uniform Val (Source.mergedValArity srcs))}
    {rs : List Val} {g h : Heap} :
    Runs Λ own (TyArgs.transport hM types) srcs off osels base args values rs g h ↔
      Runs Λ own types srcs off osels base args values rs g h := by
  subst hM; exact Iff.rfl

end Source

namespace Expr

/-! ### The specification of a merged source -/

/-- The specification of the source merging the sources `srcs`, all of them acceptable: it is
structurally valid, it has the prescribed result type constructor, it has one parameter per
input value of a merged source, its parameters are the (pairwise distinct) renamed parameters
of those sources, and its body is a well-typed program as soon as the expression it ends in
is one in the variable context extended by the types the merged sources produce. -/
theorem bindSourcesAux_spec {Λ : Library} {m N : ℕ} {rename : ℕ → PVar → PVar}
    {rty : TyConsId} (hren : RenameSpec m rename) (hrty : rty.Bounded N) :
    ∀ (srcs : List Source) (vars : List PVar) (base : ℕ) (osels : List (List TyIdx))
      (body : TyArgs N → Expr) (types : TyArgs N),
      (∀ s ∈ srcs, s.Ok Λ) → Source.SelsOk srcs osels base →
      base + Source.mergedFreeArity srcs ≤ N →
      (bindSourcesAux body rename vars rty base osels srcs).Valid
      ∧ (bindSourcesAux body rename vars rty base osels srcs).params.length
          = Source.mergedValArity srcs
      ∧ (∀ x ∈ (bindSourcesAux body rename vars rty base osels srcs).paramNames,
          ∃ i y, i < srcs.length ∧ x = rename i y)
      ∧ (bindSourcesAux body rename vars rty base osels srcs).paramNames.Nodup
      ∧ ∀ (args : TeleArg (Source.mergedTeleOf srcs)) (ν : VarCtx) (τ : Ty),
          (∀ s ∈ srcs, ∀ y ∈ s.fn.paramNames, y.length ≤ m) →
          (∀ y ∈ vars, y.length ≤ m) → srcs.length ≤ vars.length →
          (∀ y τy,
            (y, τy) ∈ (bindSourcesAux body rename vars rty base osels srcs).sig.apply types →
            ν y = Part.some τy) →
          SafeProgram (ν.extend vars (Source.resTys srcs osels base types)) Λ τ (body types) →
          SafeProgram ν Λ τ
            (((bindSourcesAux body rename vars rty base osels srcs).body.apply args).apply
              types) := by
  intro srcs
  induction srcs with
  | nil =>
    intro vars base osels body types _ _ _
    refine ⟨⟨by simp, hrty⟩, rfl, by simp, by simp, ?_⟩
    intro args ν τ _ _ _ _ hcall
    rw [bindSourcesAux_nil_body]
    rwa [Source.resTys_nil, VarCtx.extend_nil] at hcall
  | cons s srcs ih =>
    intro vars base osels body types hok hsel hfit
    have hs : s.Ok Λ := hok s (by simp)
    have hsrc : s.fn.Valid := hs.src_valid
    have hfit' : base + s.freeArity + Source.mergedFreeArity srcs ≤ N := by
      rw [Source.mergedFreeArity_cons] at hfit; omega
    have hrenlt : ∀ i < s.arity, s.ren (osels.headD []) base i < N := fun i hi =>
      Source.ren_lt hsel.osel_lt hsel.length_le (by omega) hi
    set τs' := s.tyArgs (osels.headD []) base types with hτs
    obtain ⟨hvalid_t, -, hfresh_t, hnodup_t, hsafe_t⟩ :=
      ih vars.tail (base + s.freeArity) osels.tail body types
        (fun s' h => hok s' (List.mem_cons_of_mem _ h)) hsel.tail hfit'
    refine ⟨⟨?paramCons, ?tyBounded⟩, ?len, ?fresh, ?nodup, ?safe⟩
    case paramCons =>
      intro q hq
      rw [bindSourcesAux_cons_params, List.mem_append] at hq
      rcases hq with hq | hq
      · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
        obtain ⟨i, hi, hq2⟩ := hsrc.1 q' hq'
        exact ⟨s.ren (osels.headD []) base i, hrenlt i hi, by rw [hq2]; rfl⟩
      · exact hvalid_t.1 q hq
    case tyBounded => rw [bindSourcesAux_cons_ty]; exact hvalid_t.2
    case len => exact bindSourcesAux_params_length _ _ _ _
    case fresh =>
      intro x hx
      rw [bindSourcesAux_cons_paramNames, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        exact ⟨srcs.length, y, by simp, rfl⟩
      · obtain ⟨i, y, hi, rfl⟩ := hfresh_t _ hx
        exact ⟨i, y, by simp only [List.length_cons]; omega, rfl⟩
    case nodup =>
      rw [bindSourcesAux_cons_paramNames, List.nodup_append]
      refine ⟨?_, hnodup_t, ?_⟩
      · exact hs.paramNames_nodup.map_on
          (fun _ _ _ _ h => (hren.injective h).2)
      · intro x hx y hy heq
        obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, w, hi, hw⟩ := hfresh_t y hy
        rw [hw] at heq
        obtain ⟨rfl, -⟩ := hren.injective heq
        omega
    case safe =>
      intro args ν τ hsrclen hvarlen hlen hctx hcall
      cases vars with
      | nil => simp at hlen
      | cons x xs =>
        rw [bindSourcesAux_cons_body]
        simp only [List.headD_cons, List.tail_cons]
        have hsig := bindSourcesAux_cons_sig (rename := rename) (vars := x :: xs)
          (body := body) (rty := rty) (base := base) (osels := osels) (s := s)
          (srcs := srcs) hsrc types
        simp only [List.tail_cons, ← hτs] at hsig
        obtain ⟨hbodysafe, -, hnodup⟩ := hs.concretise_typechecks args.fst τs'
        have hmapfst : ((s.fn.sig.apply τs').map Prod.fst) = s.fn.paramNames :=
          FunTempl.sig_map_fst
        refine ⟨s.fn.resTy.apply τs', ?_, ?_⟩
        · have halias := bindAliases_safeProgram (n := srcs.length) hren
            (ps := s.fn.sig.apply τs') (ν := ν) (by rw [hmapfst]; exact hsrclen s (by simp))
            (fun y τy hy => hctx _ _
              (hsig ▸ List.mem_append_left _ (List.mem_map.mpr ⟨(y, τy), hy, rfl⟩)))
            (safeProgram_subset hbodysafe (VarCtx.from_subset_extend ν hnodup))
          rwa [hmapfst] at halias
        · show SafeProgram (PFun.insert x (s.fn.resTy.apply τs') ν) Λ τ _
          refine hsafe_t args.snd (PFun.insert x (s.fn.resTy.apply τs') ν) τ
            (fun s' h => hsrclen s' (List.mem_cons_of_mem _ h))
            (fun y hy => hvarlen y (List.mem_cons_of_mem _ hy))
            (by simpa using hlen) ?_ ?_
          · intro y τy hy
            have hyx : y ≠ x := by
              obtain ⟨i, z, -, rfl⟩ := hfresh_t _ (FunTempl.mem_params_of_mem_sig hy)
              exact Ne.symm (hren.ne_short (hvarlen x (by simp)))
            rw [PFun.insert_apply_ne _ _ hyx]
            exact hctx _ _ (hsig ▸ List.mem_append_right _ hy)
          · rw [Source.resTys_cons, VarCtx.extend_cons] at hcall
            simpa only [List.tail_cons, List.headD_cons] using hcall

/-! ### Closedness of a merged body -/

/-- Only the parameters of a merged source and the names occurring in the expression its
body ends in are free in that body. -/
private theorem bindSourcesAux_closed {Λ : Library} {m N : ℕ} {rename : ℕ → PVar → PVar}
    {rty : TyConsId} :
    ∀ (srcs : List Source) (vars : List PVar) (base : ℕ) (osels : List (List TyIdx))
      (body : TyArgs N → Expr) (args : TeleArg (Source.mergedTeleOf srcs))
      (types : TyArgs N),
      (∀ s ∈ srcs, s.Ok Λ) → (∀ ts, (body ts).Closed {y : PVar | y.length ≤ m}) →
      (((bindSourcesAux body rename vars rty base osels srcs).body.apply args).apply
          types).Closed
        ({y : PVar | y.length ≤ m}
          ∪ {y | y ∈ (bindSourcesAux body rename vars rty base osels srcs).paramNames}) := by
  intro srcs
  induction srcs with
  | nil =>
    intro vars base osels body args types _ hbody
    rw [bindSourcesAux_nil_body]
    exact Expr.Closed.mono (hbody types) Set.subset_union_left
  | cons s srcs ih =>
    intro vars base osels body args types hok hbody
    rw [bindSourcesAux_cons_body, bindSourcesAux_cons_paramNames]
    refine ⟨(bindAliases_closed {y : PVar | y.length ≤ m} s.fn.paramNames
        (((hok s (by simp)).body_closed args.fst _).mono Set.subset_union_right)).mono ?_,
      (ih vars.tail (base + s.freeArity) osels.tail body args.snd _
        (fun s' h => hok s' (List.mem_cons_of_mem _ h)) hbody).mono ?_⟩ <;>
      intro z hz <;> simp at hz ⊢ <;> aesop

/-- Substituting one of the let-bound variables of a merged body reaches the expression that
body ends in. -/
private theorem bindSourcesAux_substTerm {Λ : Library} {m N : ℕ} {rename : ℕ → PVar → PVar}
    {rty : TyConsId} {x : PVar} {v : Val} (hren : RenameSpec m rename) :
    ∀ (srcs : List Source) (vars : List PVar) (base : ℕ) (osels : List (List TyIdx))
      (body : TyArgs N → Expr) (args : TeleArg (Source.mergedTeleOf srcs))
      (types : TyArgs N),
      (∀ s ∈ srcs, s.Ok Λ) → x ∉ vars → x.length ≤ m →
      srcs.length ≤ vars.length →
      ((((bindSourcesAux body rename vars rty base osels srcs).body.apply args).apply
          types).substTerm x (.val v))
        = (((bindSourcesAux (fun ts => (body ts).substTerm x (.val v)) rename vars rty base
            osels srcs).body.apply args).apply types) := by
  intro srcs
  induction srcs with
  | nil =>
    intro vars base osels body args types _ _ _ _
    rw [bindSourcesAux_nil_body, bindSourcesAux_nil_body]
  | cons s srcs ih =>
    intro vars base osels body args types hok hx hxlen hlen
    cases vars with
    | nil => simp at hlen
    | cons y ys =>
      have hy : y ≠ x := fun h => hx (by simp [h])
      rw [bindSourcesAux_cons_body, bindSourcesAux_cons_body]
      simp only [List.headD_cons, List.tail_cons, Expr.substTerm, Binder.named.injEq, hy,
        if_false]
      have halias := bindAliases_closed (rename := rename srcs.length) ∅
        s.fn.paramNames
        (Expr.Closed.mono ((hok s (by simp)).body_closed args.fst
          (s.tyArgs (osels.headD []) base types))
          Set.subset_union_right)
      rw [Expr.Closed.subst_eq (.val v) halias (by
          rintro (hz | hz)
          · exact hz
          · obtain ⟨w, -, hw⟩ := List.mem_map.mp hz
            exact hren.ne_short hxlen hw.symm),
        ih ys (base + s.freeArity) osels.tail body args.snd _
          (fun s' h => hok s' (List.mem_cons_of_mem _ h))
          (fun h => hx (List.mem_cons_of_mem _ h)) hxlen (by simpa using hlen)]

/-- Substituting let-bound variables of a merged body reaches the expression that body ends
in: the iterated form of `bindSourcesAux_substTerm`. -/
theorem bindSourcesAux_substs {Λ : Library} {m N : ℕ} {rename : ℕ → PVar → PVar}
    {rty : TyConsId} (hren : RenameSpec m rename) (srcs : List Source) (vars : List PVar)
    (base : ℕ) (osels : List (List TyIdx)) (args : TeleArg (Source.mergedTeleOf srcs))
    (types : TyArgs N) (hok : ∀ s ∈ srcs, s.Ok Λ) (hlen : srcs.length ≤ vars.length) :
    ∀ (xs : List PVar) (vs : List Val) (body : TyArgs N → Expr),
      (∀ x ∈ xs, x ∉ vars) → (∀ x ∈ xs, x.length ≤ m) →
      ((((bindSourcesAux body rename vars rty base osels srcs).body.apply args).apply
          types).substs xs (Term.ofVals vs))
        = (((bindSourcesAux (fun ts => (body ts).substs xs (Term.ofVals vs)) rename vars rty
            base osels srcs).body.apply args).apply types) := by
  intro xs
  induction xs with
  | nil => intro vs body _ _; rfl
  | cons x xs ih =>
    intro vs body hvars hxs
    cases vs with
    | nil => simp
    | cons v vs =>
      rw [Term.ofVals_cons, Expr.substs_cons,
        bindSourcesAux_substTerm hren srcs vars base osels body args types hok
          (hvars x (by simp)) (hxs x (by simp)) hlen,
        ih vs _ (fun y hy => hvars y (List.mem_cons_of_mem _ hy))
          (fun y hy => hxs y (List.mem_cons_of_mem _ hy))]
      rfl

/-! ### The behaviour of a merged body -/

/-- The body of a merged source, run on the resources required by its parameters, reproduces
the behaviour of the expression it ends in on the results of the merged sources. -/
theorem bindSourcesAux_frameStep {Λ : Library} {m N : ℕ} {rename : ℕ → PVar → PVar}
    {own : TyConsId → ℕ → Val → Asrt.{0}}
    {rty : TyConsId} (hren : RenameSpec m rename) (hrty : rty.Bounded N) :
    ∀ (srcs : List Source) (vars : List PVar) (off : TyConsId → ℕ) (base : ℕ)
      (osels : List (List TyIdx))
      (body : TyArgs N → Expr) (args : TeleArg (Source.mergedTeleOf srcs))
      (types : TyArgs N)
      (values : TeleArg (Tele.uniform Val (Source.mergedValArity srcs)))
      (rs : List Val) (g hF h h' : Heap) (εₛ : Exit),
      (∀ s ∈ srcs, s.Ok Λ) →
      (∀ s ∈ srcs, ∀ y ∈ s.fn.paramNames, y.length ≤ m) →
      (∀ y ∈ vars, y.length ≤ m) → vars.Nodup → srcs.length ≤ vars.length →
      (∀ ts, (body ts).Closed {y : PVar | y.length ≤ m}) →
      Source.SelsOk srcs osels base → base + Source.mergedFreeArity srcs ≤ N →
      hF ##ₘ h →
      Source.Runs Λ own types srcs off osels base args values rs g h →
      (Λ ⊢ ⟨hF ∪ h | (body types).substs vars (Term.ofVals rs)⟩ ⇓ᵢ ⟨h' | εₛ⟩) →
      HProp g (FunTempl.ownValsAt own off
            (bindSourcesAux body rename vars rty base osels srcs).paramCons
            values.toList)
        ∧ hF ##ₘ g
        ∧ Λ ⊢ ⟨hF ∪ g |
            (((bindSourcesAux body rename vars rty base osels srcs).body.apply args).apply
                types).substs
              (bindSourcesAux body rename vars rty base osels srcs).paramNames
              (Term.ofVals values.toList)⟩ ⇓ᵢ ⟨h' | εₛ⟩ := by
  intro srcs
  induction srcs with
  | nil =>
    intro vars off base osels body args types values rs g hF h h' εₛ
      _ _ _ _ _ _ _ _ _ hruns hstep
    obtain ⟨rfl, rfl, rfl⟩ := hruns
    refine ⟨?_, PFun.disjoint_empty_right hF, ?_⟩
    · simp [FunTempl.ownValsAt, FunTempl.paramCons]
    · rw [bindSourcesAux_nil_body,
        FunTempl.paramNames_eq_nil bindSourcesAux_nil_params, Expr.substs_nil_left]
      simpa using hstep
  | cons s srcs ih =>
    intro vars off base osels body args types values rs g hF h h' εₛ hok hsrclen hvarlen hdup
      hlen hbody hsel hfit hdisj hruns hstep
    obtain ⟨r, rs', g₁, g₂, h₁, h₂, rfl, rfl, rfl, hdisj12, hpre1, hstep1, hruns2⟩ := hruns
    cases vars with
    | nil => simp at hlen
    | cons x xs =>
    have hs : s.Ok Λ := hok s (by simp)
    have hok' : ∀ s' ∈ srcs, s'.Ok Λ := fun s' hm => hok s' (List.mem_cons_of_mem _ hm)
    have hfit' : base + s.freeArity + Source.mergedFreeArity srcs ≤ N := by
      rw [Source.mergedFreeArity_cons] at hfit; omega
    obtain ⟨hFd1, hFd2⟩ := PFun.disjoint_union_right.mp hdisj
    rw [Term.ofVals_cons, Expr.substs_cons] at hstep
    obtain ⟨hpre2, hdisjp2, hstep2⟩ := ih xs
      (TyConsId.offAfter off (s.renCons (osels.headD []) base)) (base + s.freeArity) osels.tail
      (fun ts => (body ts).substTerm x (.val r)) args.snd types
      (TeleArg.splitUniform s.fn.params.length (Source.mergedValArity srcs) values).2
      rs' g₂ (hF ∪ h₁) h₂ h' εₛ hok'
      (fun s' hm => hsrclen s' (List.mem_cons_of_mem _ hm))
      (fun y hy => hvarlen y (List.mem_cons_of_mem _ hy))
      (List.nodup_cons.mp hdup).2 (by simpa using hlen)
      (fun ts => Expr.Closed.subst_val x r (hbody ts))
      hsel.tail hfit'
      (PFun.disjoint_union_left.mpr ⟨hFd2, hdisj12⟩)
      hruns2
      (by rw [PFun.union_assoc]; exact hstep)
    rw [bindSourcesAux_paramCons_tail_irrel (fun ts => (body ts).substTerm x (.val r)) body]
      at hpre2
    rw [bindSourcesAux_paramNames_tail_irrel (fun ts => (body ts).substTerm x (.val r)) body]
      at hstep2
    have hdisjp2' := PFun.disjoint_union_left.mp hdisjp2
    have hdisj1 : h₁ ##ₘ (hF ∪ g₂) :=
      PFun.disjoint_union_right.mpr ⟨hFd1.symm, hdisjp2'.2⟩
    obtain ⟨hstep1F, hg1disj⟩ := (frame_addition hstep1 (hF ∪ g₂) hdisj1).resolve_right
      (by rintro ⟨l, hl, -⟩; simp at hl)
    have hg1disj' := PFun.disjoint_union_right.mp hg1disj
    have hparamsdup : s.fn.paramNames.Nodup := hs.paramNames_nodup
    have hlen1 : s.fn.paramNames.length
        = (TeleArg.splitUniform s.fn.params.length
            (Source.mergedValArity srcs) values).1.toList.length := by
      simp [FunTempl.paramNames]
    refine ⟨?_, ?_, ?_⟩
    · simp only [FunTempl.paramNames, List.length_map] at hlen1
      rw [FunTempl.ownValsAt, ← splitUniform_toList s.fn.params.length
          (Source.mergedValArity srcs) values,
        bindSourcesAux_cons_paramCons, ← Source.renCons,
        TyConsId.ranksFrom_append,
        List.zip_append (by
          rw [TyConsId.length_ranksFrom, Source.length_renCons]
          simp), hProp_iter_append]
      refine ⟨g₁, g₂, rfl, hg1disj'.2, hpre1, ?_⟩
      simpa only [List.tail_cons] using hpre2
    · exact PFun.disjoint_union_right.mpr ⟨hg1disj'.1.symm, hdisjp2'.1⟩
    · rw [bindSourcesAux_cons_body, bindSourcesAux_cons_paramNames]
      simp only [List.headD_cons, List.tail_cons]
      rw [← splitUniform_toList s.fn.params.length (Source.mergedValArity srcs) values,
        Term.ofVals_append, Expr.substs_append _ (by simpa using hlen1)]
      have hxfresh : x ∉ s.fn.paramNames.map (rename srcs.length) := by
        intro hmem
        obtain ⟨w, -, heq⟩ := List.mem_map.mp hmem
        exact hren.ne_short (hvarlen x (by simp)) heq.symm
      have hfresh_t := (bindSourcesAux_spec (Λ := Λ) (rename := rename) (rty := rty) hren hrty
        srcs xs (base + s.freeArity) osels.tail body types hok' hsel.tail hfit').2.2.1
      have hxrest : x ∉ (bindSourcesAux body rename xs rty (base + s.freeArity)
          osels.tail srcs).paramNames := fun hmem => by
        obtain ⟨i, z, -, heq⟩ := hfresh_t x hmem
        exact hren.ne_short (hvarlen x (by simp)) heq
      rw [Expr.substs_letIn_named hxfresh, Expr.substs_letIn_named hxrest]
      have hchainclosed := bindSourcesAux_closed (rename := rename) (rty := rty)
        srcs xs (base + s.freeArity) osels.tail body args.snd types hok' hbody
      rw [Expr.Closed.substs_eq hchainclosed (by
        intro y hy
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hy
        rintro (hz | hz)
        · exact hren.ne_short hz rfl
        · obtain ⟨i, z, hi, heq⟩ := hfresh_t _ hz
          obtain ⟨rfl, -⟩ := hren.injective heq
          omega)]
      have healias : ((bindAliases (s.fn.body.apply args.fst |>.apply
            (s.tyArgs (osels.headD []) base types))
            (rename srcs.length) s.fn.paramNames).substs
          (s.fn.paramNames.map (rename srcs.length))
          (Term.ofVals
            (TeleArg.splitUniform s.fn.params.length
              (Source.mergedValArity srcs) values).1.toList)).Closed ∅ := by
        refine Expr.Closed.substs_erase ?_ (by simpa using hlen1)
        refine Expr.Closed.mono (bindAliases_closed ∅ s.fn.paramNames
          (Expr.Closed.mono (hs.body_closed args.fst _) Set.subset_union_right))
          fun z hz => Or.inr (hz.resolve_left id)
      rw [Expr.Closed.substs_eq healias (fun y _ => by simp)]
      refine FrameStep.letIn (v := r) (h'' := h₁ ∪ (hF ∪ g₂)) ?_ ?_
      · refine bindAliases_frameStep (n := srcs.length) hren s.fn.paramNames
          (TeleArg.splitUniform s.fn.params.length (Source.mergedValArity srcs) values).1.toList
          ((s.fn.body.apply args.fst).apply (s.tyArgs (osels.headD []) base types)) ∅
          (hF ∪ (g₁ ∪ g₂)) (h₁ ∪ (hF ∪ g₂)) (.ok r)
          hparamsdup hlen1 (hsrclen s (by simp)) (by simp)
          (Expr.Closed.mono (hs.body_closed args.fst _) Set.subset_union_right) ?_
        rw [show hF ∪ (g₁ ∪ g₂) = g₁ ∪ (hF ∪ g₂) by
          rw [← PFun.union_assoc, ← PFun.union_assoc, PFun.union_comm hg1disj'.1.symm]]
        exact hstep1F
      · show FrameStep Λ (h₁ ∪ (hF ∪ g₂)) (Expr.substTerm _ x (.val r)) h' εₛ
        rw [Expr.substTerm_substs_comm hxrest,
          bindSourcesAux_substTerm hren srcs xs (base + s.freeArity) osels.tail body args.snd
            types hok' (List.nodup_cons.mp hdup).1 (hvarlen x (by simp)) (by simpa using hlen)]
        rw [show h₁ ∪ (hF ∪ g₂) = (hF ∪ h₁) ∪ g₂ by
          rw [← PFun.union_assoc, PFun.union_comm hFd1.symm]]
        exact hstep2

end Expr

end RUXt
