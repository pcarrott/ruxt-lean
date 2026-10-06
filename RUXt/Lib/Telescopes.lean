import Mathlib.Tactic

/-!
# Telescopes
A telescope `Tele` describes a dependent context: a sequence of binders, each of whose types
may depend on the values of the earlier ones.  It is first-class data, so contexts can be
computed and inspected (`Tele.uniform`, `Tele.app`, `Tele.ulift`, the `[tele ...]` notation).

Given a telescope `TT`:

* `TeleArg TT` is the type of *environments* of `TT`: one value for each binder, i.e. the
  nested dependent pair `Σ x₁, Σ x₂, …, PUnit`.  Environments are built with anonymous
  constructors `⟨x₁, x₂, …, PUnit.unit⟩` and taken apart with projections or, preferably,
  patterns: `fun ⟨x₁, x₂, _⟩ => b` destructures an environment of a two-binder telescope.
  `TeleArg.app`/`fst`/`snd` join and split environments of an appended telescope.  The
  `*Uniform`/`toList`/`ofList` operations treat environments of a uniform telescope as lists.
* An object parameterised by the context `TT` is an ordinary function `TeleArg TT → A`.
  Instantiating it with an environment is plain function application.  `A` may live in any
  universe, so no lifting is needed for small result types.

## Universe polymorphism
A telescope `Tele.{u}` stores binder types in `Type u`.  A binder of a smaller type is lifted
into `Type u` (`Lifted`, or `Tele.ulift` for a whole telescope); this cannot be avoided, since
Lean has no cumulativity.  Result types never need lifting, since a parameterised object is a
function of `TeleArg TT`.
-/

namespace RUXt

universe u v w b

/-- A telescope: an inductively defined, possibly dependent, sequence of argument types.
The binder types live in an arbitrary universe `Type u`. -/
inductive Tele : Type (u + 1) where
  /-- The empty telescope (`TeleO`). -/
  | nil : Tele
  /-- Extend a telescope by a fresh argument of type `X`, whose value may influence the
  remaining telescope `binder x` (`TeleS`). -/
  | cons {X : Type u} (binder : X → Tele) : Tele

/-- A uniform telescope containing exactly `N` arguments of type `A`. -/
def Tele.uniform (X : Type u) : ℕ → Tele
  | 0 => .nil
  | n + 1 => .cons (fun _ : X => Tele.uniform X n)

/-- The environments of a telescope `TT`: one value for each binder, as the nested dependent pair
`Σ x₁, Σ x₂, …, PUnit`. -/
def TeleArg : Tele.{u} → Type u
  | Tele.nil => PUnit
  | Tele.cons binder => Σ x, TeleArg (binder x)

def TeleArg.replicate {X : Type _} (N : ℕ) (x : X) : TeleArg (Tele.uniform X N) :=
  match N with
  | 0 => .unit
  | N + 1 => ⟨x, replicate N x⟩

/-- Insert an extra argument at position `i` of an argument tuple for a uniform telescope
(at the end, if `i` is past the end of the tuple). -/
def TeleArg.insertUniform {X : Type u} (x : X) : (i : ℕ) → {n : ℕ} →
    TeleArg (Tele.uniform X n) → TeleArg (Tele.uniform X (n + 1))
  | 0, _, args => ⟨x, args⟩
  | _ + 1, 0, _ => ⟨x, PUnit.unit⟩
  | i + 1, _ + 1, args => ⟨args.1, insertUniform x i args.2⟩

/-- Insert an extra argument at position `i` of an argument tuple for a uniform telescope
of length `n - 1`, producing a tuple of length `n`.  When `n = 0` there is nothing to
extend and the argument is dropped. -/
def TeleArg.insertUniformPred {X : Type u} (x : X) (i : ℕ) : {n : ℕ} →
    TeleArg (Tele.uniform X (n - 1)) → TeleArg (Tele.uniform X n)
  | 0, _ => PUnit.unit
  | _ + 1, args => TeleArg.insertUniform x i args

/-- A small type, lifted into the universe `u` of a telescope.  Used for binders of small type
(e.g. `[tele (l : Lifted Loc)]` in a `Tele.{1}`). -/
abbrev Lifted (A : Type) : Type u := ULift.{u, 0} A

/-- Concatenate two telescopes. -/
def Tele.app : Tele.{u} → Tele.{u} → Tele.{u}
  | Tele.nil, tt2 => tt2
  | Tele.cons b, tt2 => Tele.cons (fun x => app (b x) tt2)

/-- Combine argument tuples for two appended telescopes. -/
def TeleArg.app : {tt1 tt2 : Tele.{u}} → TeleArg tt1 → TeleArg tt2 →
    TeleArg (tt1.app tt2)
  | .nil, _, _, arg2 => arg2
  | .cons _, _, arg1, arg2 => ⟨arg1.1, TeleArg.app arg1.2 arg2⟩

/-- Project the first component of an argument tuple for an appended telescope. -/
def TeleArg.fst : {tt1 tt2 : Tele.{u}} → TeleArg (tt1.app tt2) → TeleArg tt1
  | Tele.nil, _, _ => PUnit.unit
  | Tele.cons _, _, arg => ⟨arg.1, TeleArg.fst arg.2⟩

/-- Project the second component of an argument tuple for an appended telescope. -/
def TeleArg.snd : {tt1 tt2 : Tele.{u}} → TeleArg (tt1.app tt2) → TeleArg tt2
  | Tele.nil, _, arg => arg
  | Tele.cons _, _, arg => TeleArg.snd arg.2

/-- Reassociate an argument tuple for an appended telescope: `a ++ (b ++ c)` becomes
`(a ++ b) ++ c`.  The arguments stay in the same order. -/
def TeleArg.assoc {tt1 tt2 tt3 : Tele.{u}} (arg : TeleArg (tt1.app (tt2.app tt3))) :
    TeleArg ((tt1.app tt2).app tt3) :=
  (arg.fst.app arg.snd.fst).app arg.snd.snd

/-- Collect the arguments of a uniform value telescope in left-to-right order. -/
def TeleArg.toList {X : Type _} : {N : ℕ} → TeleArg (Tele.uniform X N) → List X
  | 0, _ => []
  | _ + 1, ⟨arg, rest⟩ => arg :: toList rest

@[simp] theorem TeleArg.toList_length {X : Type _} :
    ∀ {N : ℕ} (args : TeleArg (Tele.uniform X N)), args.toList.length = N := by
  intro N
  induction N with
  | zero => intro args; rfl
  | succ n ih =>
    intro args
    obtain ⟨a, rest⟩ := args
    simp [TeleArg.toList, ih rest]

/-- Map a function over every component of a uniform argument tuple. -/
def TeleArg.mapUniform {X : Type u} {Y : Type b} (f : X → Y) :
    {N : ℕ} → TeleArg (Tele.uniform X N) → TeleArg (Tele.uniform Y N)
  | 0, _ => PUnit.unit
  | _ + 1, a => ⟨f a.1, mapUniform f a.2⟩

/-- Turn a list into an argument tuple for the uniform telescope of matching length. -/
def TeleArg.ofList {X : Type u} : (l : List X) → TeleArg (Tele.uniform X l.length)
  | [] => PUnit.unit
  | x :: xs => ⟨x, ofList xs⟩

/-- Prepend an argument to an argument tuple for a uniform telescope. -/
def TeleArg.consUniform {X : Type _} {n : ℕ} (x : X) (a : TeleArg (Tele.uniform X n)) :
    TeleArg (Tele.uniform X (n + 1)) :=
  ⟨x, a⟩

/-- Concatenate two argument tuples for uniform telescopes. -/
def TeleArg.appendUniform {X : Type _} {n m : ℕ} (a : TeleArg (Tele.uniform X n))
    (b : TeleArg (Tele.uniform X m)) : TeleArg (Tele.uniform X (n + m)) :=
  (by simp : (a.toList ++ b.toList).length = n + m) ▸ TeleArg.ofList (a.toList ++ b.toList)

/-- The argument tuple of the first `n` entries of a list, padded with `dflt` if the list is
too short. -/
def TeleArg.ofListPad {X : Type _} (dflt : X) (n : ℕ) (l : List X) :
    TeleArg (Tele.uniform X n) :=
  (by simp : ((l ++ List.replicate n dflt).take n).length = n) ▸
    TeleArg.ofList ((l ++ List.replicate n dflt).take n)

/-- The tuple for a uniform telescope of length `n` read off the tuple `a` along the renaming
`ρ` of positions: position `i` receives the argument of `a` at position `ρ i`, and positions
`ρ i` beyond `a` get `dflt`. -/
def TeleArg.reindex {X : Type _} (dflt : X) (ρ : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (a : TeleArg (Tele.uniform X m)) : TeleArg (Tele.uniform X n) :=
  TeleArg.ofListPad dflt n ((List.range n).map fun i => a.toList.getD (ρ i) dflt)

/-- The block of `len` consecutive arguments of a tuple for a uniform telescope, starting at
position `start`; positions beyond the tuple get `dflt`.  This is reindexing along the shift
by `start`. -/
def TeleArg.block {X : Type _} (dflt : X) {n : ℕ} (a : TeleArg (Tele.uniform X n))
    (start len : ℕ) : TeleArg (Tele.uniform X len) :=
  a.reindex dflt (start + ·) len

/-- Split a uniform telescope at a specified length. -/
def TeleArg.splitUniform {X : Type _} (n m : ℕ) (args : TeleArg (Tele.uniform X (n + m))) :
    TeleArg (Tele.uniform X n) × TeleArg (Tele.uniform X m) := by
  induction n with
  | zero => exact ⟨.unit, cast (by simp) args⟩
  | succ n ih =>
      obtain ⟨argₓ, args⟩ : TeleArg (Tele.cons (fun _ : X => Tele.uniform X (n + m))) :=
        cast (by simp [Nat.succ_add, Tele.uniform]) args
      obtain ⟨argsₙ, argsₘ⟩ := ih args
      exact (⟨argₓ, argsₙ⟩, argsₘ)

/-! ### Lifting a telescope into a higher universe -/

/-- Lift a telescope into a higher universe: every binder type is replaced by its `ULift`. -/
def Tele.ulift : Tele.{v} → Tele.{max v w}
  | Tele.nil => Tele.nil
  | Tele.cons (X := X) binder => Tele.cons fun x : ULift.{w, v} X => (binder x.down).ulift

/-- Read an argument tuple for a lifted telescope as one for the telescope itself. -/
def TeleArg.ulower : {tt : Tele.{v}} → TeleArg (Tele.ulift.{v, w} tt) → TeleArg tt
  | Tele.nil, _ => PUnit.unit
  | Tele.cons _, arg => ⟨arg.1.down, TeleArg.ulower arg.2⟩

/-- Lift an argument tuple along the lifting of its telescope. -/
def TeleArg.uliftArg : {tt : Tele.{v}} → TeleArg tt → TeleArg (Tele.ulift.{v, w} tt)
  | Tele.nil, _ => PUnit.unit
  | Tele.cons _, arg => ⟨ULift.up arg.1, TeleArg.uliftArg arg.2⟩

/-!
## The `[tele ...]` notation
We provide a term notation `[tele (x : A) (y : B) ...]` for *building* a telescope value,
i.e. an element of `Tele`. It expands to the corresponding chain of `Tele.cons`/`Tele.nil`:
```
[tele (x : A) (y : B)]  ↝  Tele.cons (fun x : A => Tele.cons (fun y : B => Tele.nil))
[tele]                  ↝  Tele.nil
```
The binders may be dependent (e.g. `[tele (n : Nat) (_ : Fin n)]`) and `_` is allowed for
anonymous binders.

Note on tokenisation: we keep `[` and `tele` as two separate tokens rather than a
single `[tele` atom.  A single `[tele` atom would be lexed greedily and would break
ordinary list literals whose first element is an identifier starting with `tele` (e.g.
`[telescope, x]`).  Keeping them separate makes `tele` a keyword that only triggers
the notation right after an opening `[`, while still allowing such list literals. -/
open Lean Parser Term in
syntax (name := teleNotation) "[" "tele" (ppSpace funBinder)* "]" : term
macro_rules
  | `([tele $bs:funBinder*]) => do
      let mut e ← `(RUXt.Tele.nil)
      for b in bs.reverse do
        e ← `(RUXt.Tele.cons (fun $b => $e))
      return e

/-! ## Properties -/

@[simp] theorem TeleArg.fst_append {tt1 tt2 : Tele.{u}}
    (arg1 : TeleArg tt1) (arg2 : TeleArg tt2) :
    (arg1.app arg2).fst = arg1 := by
  induction tt1 with
  | nil => cases arg1; rfl
  | cons binder ih =>
    obtain ⟨x, rest⟩ := arg1
    simp [TeleArg.app, TeleArg.fst, ih x]

@[simp] theorem TeleArg.snd_append {tt1 tt2 : Tele.{u}}
    (arg1 : TeleArg tt1) (arg2 : TeleArg tt2) :
    (arg1.app arg2).snd = arg2 := by
  induction tt1 with
  | nil => rfl
  | cons binder ih =>
    obtain ⟨x, rest⟩ := arg1
    simp [TeleArg.app, TeleArg.snd, ih x]

/-- An argument tuple for an appended telescope is determined by its two projections. -/
@[simp] theorem TeleArg.app_fst_snd : ∀ {tt1 tt2 : Tele} (arg : TeleArg (tt1.app tt2)),
    arg.fst.app arg.snd = arg := by
  intro tt1
  induction tt1 with
  | nil => intro tt2 arg; rfl
  | cons binder ih =>
    intro tt2 arg
    obtain ⟨x, rest⟩ := arg
    simp [TeleArg.app, TeleArg.fst, TeleArg.snd, ih x rest]

@[simp] theorem TeleArg.toList_mapUniform {X : Type u} {Y : Type b} (f : X → Y) :
    ∀ {N : ℕ} (a : TeleArg (Tele.uniform X N)),
      (a.mapUniform f).toList = a.toList.map f
  | 0, _ => rfl
  | _ + 1, a => by
      show f a.1 :: (a.2.mapUniform f).toList = f a.1 :: a.2.toList.map f
      rw [toList_mapUniform f a.2]

@[simp] theorem TeleArg.mapUniform_replicate {X : Type u} {Y : Type b} (f : X → Y) (x : X) :
    ∀ N : ℕ, (TeleArg.replicate N x).mapUniform f = TeleArg.replicate N (f x)
  | 0 => rfl
  | N + 1 => by
      show (⟨f x, (TeleArg.replicate N x).mapUniform f⟩ :
          TeleArg (Tele.uniform Y (N + 1))) = ⟨f x, TeleArg.replicate N (f x)⟩
      rw [mapUniform_replicate f x N]

@[simp] theorem TeleArg.toList_ofList {X : Type _} (l : List X) :
    (TeleArg.ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [TeleArg.ofList, TeleArg.toList, ih]

/-- Argument tuples for a uniform telescope are determined by their list of arguments. -/
theorem TeleArg.toList_injective {X : Type _} :
    ∀ {N : ℕ} (a b : TeleArg (Tele.uniform X N)), a.toList = b.toList → a = b := by
  intro N
  induction N with
  | zero => intro a b _; cases a; cases b; rfl
  | succ n ih =>
    intro a b h
    obtain ⟨x, as⟩ := a
    obtain ⟨y, bs⟩ := b
    simp only [TeleArg.toList, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [ih as bs h]

/-- Transporting an argument tuple along an equality of lengths does not change its list of
arguments. -/
@[simp] theorem TeleArg.toList_transport {X : Type _} {M N : ℕ} (h : M = N)
    (x : TeleArg (Tele.uniform X M)) :
    (h ▸ x : TeleArg (Tele.uniform X N)).toList = x.toList := by
  subst h; rfl

@[simp] theorem TeleArg.toList_consUniform {X : Type _} {n : ℕ} (x : X)
    (a : TeleArg (Tele.uniform X n)) : (a.consUniform x).toList = x :: a.toList :=
  rfl

@[simp] theorem TeleArg.toList_appendUniform {X : Type _} {n m : ℕ}
    (a : TeleArg (Tele.uniform X n)) (b : TeleArg (Tele.uniform X m)) :
    (a.appendUniform b).toList = a.toList ++ b.toList := by
  rw [TeleArg.appendUniform, TeleArg.toList_transport, TeleArg.toList_ofList]

/-- A list of the expected length is recovered from its padded argument tuple. -/
@[simp] theorem TeleArg.toList_ofListPad {X : Type _} (dflt : X) {n : ℕ} {l : List X}
    (h : l.length = n) : (TeleArg.ofListPad dflt n l).toList = l := by
  rw [TeleArg.ofListPad, TeleArg.toList_transport, TeleArg.toList_ofList, ← h,
    List.take_left']
  simp

theorem splitUniform_toList {X : Type _} (n m : ℕ)
    (types : TeleArg (.uniform X (n + m))) :
    (types.splitUniform n m).1.toList ++ (types.splitUniform n m).2.toList = types.toList := by
  have uniform_injective : ∀ n n' : ℕ, Tele.uniform X n = Tele.uniform X n' →
      ∀ args : TeleArg (Tele.uniform X n), n = n' := by
    intro n
    induction n with
    | zero => rintro ⟨⟩ h _; rfl; contradiction
    | succ n ih =>
      intro n' h args
      cases n' with
      | zero => simp [Tele.uniform] at h
      | succ n =>
        simp [Tele.uniform] at h
        cases args with
        | mk x snd => rw [ih n (congrFun h x) snd]
  have cast_toList : ∀ (N N' : ℕ) (h : Tele.uniform X N = Tele.uniform X N') (x : TeleArg (Tele.uniform X N)),
      (cast (congrArg TeleArg h) x).toList = x.toList := by
    intro N N' h x
    have : N = N' := uniform_injective N N' h x
    subst this
    rfl
  induction n with
  | zero => exact cast_toList (0 + m) _ (by simp) types
  | succ n ih =>
    have h_def : TeleArg.splitUniform (n + 1) m types =
      let types' := cast (by simp [Nat.succ_add, Tele.uniform] :
          TeleArg (Tele.uniform X (n + 1 + m)) = TeleArg (Tele.cons (fun _ : X => Tele.uniform X (n + m)))) types
      let ⟨argₓ, args⟩ := types'
      let ⟨argsₙ, argsₘ⟩ := TeleArg.splitUniform n m args
      (⟨argₓ, argsₙ⟩, argsₘ) := by
      rfl
    rw [h_def]
    generalize ht : cast _ types = types'
    obtain ⟨argₓ, args⟩ := types'
    obtain hcast := cast_toList _ (n + m + 1) (by simp [Nat.succ_add]) types
    simp [TeleArg.toList, ih args, ← hcast, ht]

/-- The components of the first part of a split argument tuple: the first `n` components of
the tuple. -/
theorem TeleArg.toList_splitUniform_left {X : Type _} (n m : ℕ)
    (args : TeleArg (.uniform X (n + m))) :
    (args.splitUniform n m).1.toList = args.toList.take n := by
  conv_rhs => rw [← splitUniform_toList n m args]
  rw [List.take_left' (by simp)]

/-- The components of the second part of a split argument tuple: all but the first `n`
components of the tuple. -/
theorem TeleArg.toList_splitUniform_right {X : Type _} (n m : ℕ)
    (args : TeleArg (.uniform X (n + m))) :
    (args.splitUniform n m).2.toList = args.toList.drop n := by
  conv_rhs => rw [← splitUniform_toList n m args]
  rw [List.drop_left' (by simp)]

/-- Reading a component off the first part of a split argument tuple: the first `n`
components of the tuple are the ones of that part. -/
theorem TeleArg.getD_toList_splitUniform_left {X : Type _} (d : X) {n m : ℕ}
    (args : TeleArg (.uniform X (n + m))) {i : ℕ} (hi : i < n) :
    ((args.splitUniform n m).1.toList).getD i d = args.toList.getD i d := by
  have hlt : i < ((args.splitUniform n m).1.toList).length := by
    rw [TeleArg.toList_length]; exact hi
  rw [← splitUniform_toList n m args]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]

/-- Lifting an argument tuple and reading it back recovers the tuple. -/
@[simp] theorem TeleArg.ulower_uliftArg : ∀ {tt : Tele.{v}} (arg : TeleArg tt),
    TeleArg.ulower (TeleArg.uliftArg.{v, w} arg) = arg := by
  intro tt
  induction tt with
  | nil => intro arg; cases arg; rfl
  | cons binder ih =>
      rintro ⟨x, rest⟩
      rw [TeleArg.uliftArg, TeleArg.ulower, ih x rest]

/-- Reading an argument tuple for a lifted telescope and lifting it back recovers the
tuple. -/
@[simp] theorem TeleArg.uliftArg_ulower :
    ∀ {tt : Tele.{v}} (arg : TeleArg (Tele.ulift.{v, w} tt)),
      TeleArg.uliftArg (TeleArg.ulower arg) = arg := by
  intro tt
  induction tt with
  | nil => intro arg; cases arg; rfl
  | cons binder ih =>
      rintro ⟨x, rest⟩
      rw [TeleArg.ulower, TeleArg.uliftArg, ih x.down rest]

/-! ### Reading an argument off a tuple with an inserted argument -/

/-- The arguments of a tuple with an extra argument inserted at position `i`: at `i` the new
argument, before it the arguments of the original tuple and after it the following ones. -/
theorem TeleArg.getD_toList_insertUniform {X : Type u} (x d : X) :
    ∀ (i : ℕ) {n : ℕ} (args : TeleArg (Tele.uniform X n)), i ≤ n → ∀ j : ℕ,
      ((TeleArg.insertUniform x i args).toList).getD j d
        = if j = i then x else args.toList.getD (if j < i then j else j - 1) d := by
  intro i
  induction i with
  | zero =>
    intro n args _ j
    cases j with
    | zero => rfl
    | succ j =>
      show (x :: args.toList).getD (j + 1) d = _
      simp [List.getD]
  | succ i ih =>
    intro n args hi j
    match n, args with
    | 0, _ => omega
    | n + 1, ⟨a, rest⟩ =>
      have hi' : i ≤ n := by omega
      cases j with
      | zero =>
        show (a :: _).getD 0 d = _
        simp [List.getD, TeleArg.toList]
      | succ j =>
        show (a :: (TeleArg.insertUniform x i rest).toList).getD (j + 1) d = _
        rw [List.getD_cons_succ, ih rest hi' j]
        by_cases hj : j = i
        · simp [hj]
        · rw [if_neg hj, if_neg (by omega : ¬ (j + 1 = i + 1))]
          by_cases hlt : j < i
          · rw [if_pos hlt, if_pos (by omega : j + 1 < i + 1)]
            show _ = (a :: rest.toList).getD (j + 1) d
            rw [List.getD_cons_succ]
          · rw [if_neg hlt, if_neg (by omega : ¬ (j + 1 < i + 1))]
            show rest.toList.getD (j - 1) d = (a :: rest.toList).getD (j + 1 - 1) d
            rw [show j + 1 - 1 = (j - 1) + 1 by omega, List.getD_cons_succ]

/-- The arguments of a tuple of length `n` obtained by inserting one at position `i < n` into
a tuple of length `n - 1`. -/
theorem TeleArg.getD_toList_insertUniformPred {X : Type u} (x d : X) {n : ℕ} (i : ℕ)
    (hi : i < n) (args : TeleArg (Tele.uniform X (n - 1))) (j : ℕ) :
    ((TeleArg.insertUniformPred x i (n := n) args).toList).getD j d
      = if j = i then x else args.toList.getD (if j < i then j else j - 1) d := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact TeleArg.getD_toList_insertUniform x d i args (by omega) j

/-! ### Reindexing a tuple -/

/-- The arguments of a reindexed tuple. -/
theorem TeleArg.toList_reindex {X : Type u} (dflt : X) (ρ : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (a : TeleArg (Tele.uniform X m)) :
    (a.reindex dflt ρ n).toList = (List.range n).map fun i => a.toList.getD (ρ i) dflt :=
  TeleArg.toList_ofListPad _ (by simp)

/-- Reading an argument off a reindexed tuple. -/
theorem TeleArg.getD_toList_reindex {X : Type u} (dflt : X) (ρ : ℕ → ℕ) {n m : ℕ}
    (a : TeleArg (Tele.uniform X m)) {i : ℕ} (hi : i < n) :
    (a.reindex dflt ρ n).toList.getD i dflt = a.toList.getD (ρ i) dflt := by
  rw [TeleArg.toList_reindex, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

/-- Reindexing along the identity at the length of the tuple itself — when that length is only
propositionally the expected one — keeps every argument. -/
@[simp] theorem TeleArg.toList_reindex_id {X : Type u} (dflt : X) {n m : ℕ}
    (a : TeleArg (Tele.uniform X m)) (h : m = n) :
    (a.reindex dflt id n).toList = a.toList := by
  subst h
  rw [TeleArg.toList_reindex]
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  rw [List.length_map, List.length_range] at hi
  rw [List.getElem_map, List.getElem_range, id, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem, Option.getD_some]

/-! ### Blocks of a tuple -/

/-- The arguments of a block of a tuple. -/
@[simp] theorem TeleArg.toList_block {X : Type u} (dflt : X) {n : ℕ}
    (a : TeleArg (Tele.uniform X n)) (start len : ℕ) :
    (a.block dflt start len).toList = (List.range len).map fun j => a.toList.getD (start + j) dflt :=
  TeleArg.toList_reindex _ _ _ _

/-- Reading an argument off a block of a tuple. -/
theorem TeleArg.getD_toList_block {X : Type u} (dflt : X) {n : ℕ}
    (a : TeleArg (Tele.uniform X n)) (start : ℕ) {len j : ℕ} (hj : j < len) :
    (a.block dflt start len).toList.getD j dflt = a.toList.getD (start + j) dflt := by
  rw [TeleArg.toList_block, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

/-- Arranging blocks of a tuple around an argument `x`: the first `i` arguments, then `x`, then
the `n - 1 - i` arguments following the `k` ones after the first `i`.  At a position other than
`i`, this reads the tuple at the position the kept argument came from: the same position before
`i`, and `k` positions further, past the ones skipped, after it. -/
theorem TeleArg.getD_toList_arrange {X : Type u} (dflt : X) {N n : ℕ}
    (a : TeleArg (Tele.uniform X N)) (x : X) {i : ℕ} (k : ℕ) (hi : i < n) (j : ℕ) :
    ((a.block dflt 0 i).appendUniform ((a.block dflt (i + k) (n - 1 - i)).consUniform x)
        |>.reindex dflt id n).toList.getD j dflt
      = if j = i then x
        else if j < n then a.toList.getD (if j < i then j else j - 1 + k) dflt else dflt := by
  have hlist : ((a.block dflt 0 i).appendUniform ((a.block dflt (i + k) (n - 1 - i)).consUniform x)
        |>.reindex dflt id n).toList
      = (a.block dflt 0 i).toList ++ x :: (a.block dflt (i + k) (n - 1 - i)).toList := by
    rw [TeleArg.toList_reindex_id _ _ (by omega), TeleArg.toList_appendUniform,
      TeleArg.toList_consUniform]
  rw [hlist, TeleArg.toList_block, TeleArg.toList_block,
    List.getD_eq_getElem?_getD]
  by_cases hji : j < i
  · rw [if_neg (by omega), if_pos (by omega), if_pos hji,
      List.getElem?_append_left (by simpa using hji)]
    simp [hji]
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hji)]
    by_cases hji' : j = i
    · subst hji'
      simp
    · rw [if_neg hji', if_neg hji]
      obtain ⟨m, rfl⟩ : ∃ m, j = i + 1 + m := ⟨j - i - 1, by omega⟩
      simp only [List.length_map, List.length_range,
        show i + 1 + m - i = m + 1 by omega, List.getElem?_cons_succ, List.getElem?_map]
      by_cases hm : m < n - 1 - i
      · rw [List.getElem?_range hm, if_pos (by omega)]
        simp only [Option.map_some, Option.getD_some]
        congr 1
        omega
      · rw [List.getElem?_eq_none (by simp; omega), if_neg (by omega)]
        rfl

end RUXt
