import RUXt.Lang.Types.Basic

namespace RUXt

/-!
# Type parameters: indices, tuples of type arguments, renaming and matching

Type parameters are referred to by index (`TyIdx`): the `i`-th type parameter is the type
constructor `TyConsId.param i`.  This file provides:

* `TyConsId.params c`, the list of type parameters `c` uses, in order of first occurrence and
  without repetitions, and `TyConsId.arity c`, their number;
* `TyConsId.Bounded c n` says that `c` only uses the first `n` type parameters;
* `TyConsId.concretise c τs` is the concrete type `c` produces at a tuple of type
  arguments, and `TyConsId.subst`/`TyConsId.rename` are the substitution of types and the
  renaming of indices it comes from;
* `TyConsId.instantiate c τs` is its partial counterpart at a *list* of type arguments, failing
  exactly when `c` uses a type parameter beyond the list; a bounded constructor instantiates at
  the list of a tuple to its concretisation at that tuple (`TyConsId.instantiate_toList`);
* `TyConsId.anon c` is the *anonymous form* of `c`: the same constructor with its type
  parameters renamed to `0, 1, …` in order of first occurrence, forgetting their names;
* `TyConsId.Match c C` compares two constructors *up to renaming* of the type parameters:
  it holds exactly when they have the same anonymous form, so `Pair<T, T>` does not match
  `Pair<T, U>`;
* `TyConsId.mergeRen c osel base n`, the renaming embedding the `n` type parameters of a
  template producing `c` into those of a template binding it: a parameter `c` uses is sent to
  the one `osel` prescribes for it, and the remaining, *free*, ones (`TyConsId.freeIdxs`,
  `TyConsId.freeArity`) to consecutive positions starting at `base`;
* `TyConsId.specSubst i τ`, the substitution pinning the type parameter `i` to the type
  constructor `τ`.

Tuples of type arguments are `TyArgs n`; `TyArgs.get` reads a type parameter off such a
tuple and `TeleArg.reindex` transports a tuple along a renaming of indices.
-/

/-! ### Tuples of type arguments -/

/-- A tuple of type arguments for `n` type parameters. -/
abbrev TyArgs (n : ℕ) : Type := TeleArg (Tele.uniform Ty n)

namespace TyArgs

/-- The empty tuple of type arguments, for a template without type parameters. -/
abbrev nil : TyArgs 0 := PUnit.unit

variable {m n : ℕ}

/-- The type argument supplied for the type parameter of index `i`; type parameters beyond
the tuple get the placeholder type `Ty.unit`. -/
def get (τs : TyArgs n) (i : TyIdx) : Ty := (TeleArg.toList τs).getD i Ty.unit

/-- The tuple of type arguments described by a list of types. -/
abbrev ofList (l : List Ty) : TyArgs l.length := TeleArg.ofList l

/-- The tuple of the first `n` types of a list, padded with `Ty.unit`. -/
abbrev ofListPad (n : ℕ) (l : List Ty) : TyArgs n := TeleArg.ofListPad Ty.unit n l

/-- Transport a tuple of type arguments along an equality of arities: the tuple itself is
unchanged, only the arity indexing it is rewritten. -/
def transport (h : m = n) (τs : TyArgs m) : TyArgs n := h ▸ τs

end TyArgs

/-! ### Deduplicating a list of indices -/

namespace TyIdx

/-- The distinct entries of a list of indices, in order of first occurrence. -/
def dedup : List TyIdx → List TyIdx
  | [] => []
  | i :: is => i :: (dedup is).filter (· ≠ i)

end TyIdx

namespace TyConsId

/-! ### The type parameters a constructor uses -/

mutual
/-- All type parameters occurring in a type constructor, in order and with repetitions. -/
def idxs : TyConsId → List TyIdx
  | .base _ => []
  | .param i => [i]
  | .custom _ args => idxsList args
/-- All type parameters occurring in a list of type constructors. -/
def idxsList : List TyConsId → List TyIdx
  | [] => []
  | c :: cs => c.idxs ++ idxsList cs
end

/-- The type parameters a type constructor uses, in order of first occurrence and without
repetitions. -/
def params (c : TyConsId) : List TyIdx := TyIdx.dedup c.idxs

/-- The number of type parameters a type constructor uses. -/
def arity (c : TyConsId) : ℕ := c.params.length

/-- A type constructor is *bounded* by `n` when it only uses the first `n` type
parameters. -/
def Bounded (c : TyConsId) (n : ℕ) : Prop := ∀ i ∈ c.params, i < n

instance (c : TyConsId) (n : ℕ) : Decidable (c.Bounded n) := by
  unfold Bounded; infer_instance

/-! ### Instantiation and renaming -/

mutual
/-- Rename the type parameters of a type constructor along `ρ`. -/
def rename (ρ : TyIdx → TyIdx) : TyConsId → TyConsId
  | .base kind => .base kind
  | .param i => .param (ρ i)
  | .custom name args => .custom name (renameList ρ args)
/-- Rename the type parameters of a list of type constructors along `ρ`. -/
def renameList (ρ : TyIdx → TyIdx) : List TyConsId → List TyConsId
  | [] => []
  | c :: cs => c.rename ρ :: renameList ρ cs
end

mutual
/-- Substitute a type for every type parameter of a type constructor, producing a concrete
type. -/
def subst (f : TyIdx → Ty) : TyConsId → Ty
  | .base kind => .base kind
  | .param i => f i
  | .custom name args => .custom name (substList f args)
/-- Substitute a type for every type parameter of a list of type constructors. -/
def substList (f : TyIdx → Ty) : List TyConsId → List Ty
  | [] => []
  | c :: cs => c.subst f :: substList f cs
end

/-- The concrete type a type constructor produces at a tuple of type arguments.  This is a
total operation: a type parameter beyond the tuple gets the placeholder type `Ty.unit`. -/
def concretise {n : ℕ} (c : TyConsId) (τs : TyArgs n) : Ty := c.subst (TyArgs.get τs)

/-- The concrete type a type constructor produces at a *list* of type arguments, whose length
is not recorded in its type.  Fails exactly when the constructor uses a type parameter beyond
the list; otherwise it is the concretisation at the tuple of those types
(`TyConsId.instantiate_eq_some`). -/
def instantiate (c : TyConsId) (τs : List Ty) : Option Ty :=
  if c.Bounded τs.length then some (c.concretise (TyArgs.ofList τs)) else none

/-! ### Anonymous type parameters

The *names* — the indices — a type constructor gives to its type parameters carry no
information: `Pair<T₁, T₇>` and `Pair<T₀, T₃>` are the same constructor under different
names.  Every constructor therefore has a canonical, *anonymous* form (`TyConsId.anon`), in
which the type parameter used at position `k` — positions being counted in order of first
occurrence — is the index `k`. -/

/-- The canonical renaming of the type parameters of a constructor: the type parameter used
at position `k`, in order of first occurrence, becomes the *anonymous* type parameter of
index `k`. -/
def anonRen (c : TyConsId) : TyIdx → TyIdx := fun i => c.params.idxOf i

/-- The *anonymous form* of a type constructor: the same constructor with its type parameters
renamed to `0, 1, …`, in order of first occurrence.  It forgets the names of the type
parameters and nothing else — in particular a parameter used twice stays used twice, so
`Pair<T, T>` and `Pair<T, U>` keep distinct anonymous forms. -/
def anon (c : TyConsId) : TyConsId := c.rename c.anonRen

/-- A type constructor is *in anonymous order* when the type parameters it uses are
`0, 1, …, c.arity - 1`, in order of first occurrence: it names its type parameters exactly as
its anonymous form does.  `f<T, U>(List<U>, Fun<U, T>) -> List<T>` produces a constructor in
anonymous order, `f<T, U>(List<T>, Fun<T, U>) -> List<U>` does not. -/
def InAnonOrder (c : TyConsId) : Prop := c.params = List.range c.arity

instance (c : TyConsId) : Decidable c.InAnonOrder := by unfold InAnonOrder; infer_instance

/-! ### Matching two type constructors up to renaming -/

/-- The renaming taking every type parameter of `c` to the type parameter `C` uses at the
same position. -/
def transfer (c C : TyConsId) : TyIdx → TyIdx := fun i => C.params.getD (c.params.idxOf i) 0

/-- Two type constructors *match* when they only differ by the *names* of their type
parameters: they have the same anonymous form, so each is obtained from the other by renaming
its type parameters position by position.  `Pair<T, T>` does not match `Pair<T, U>`. -/
def Match (c C : TyConsId) : Prop := c.anon = C.anon

instance (c C : TyConsId) : Decidable (c.Match C) := by unfold Match; infer_instance

/-! ### Embedding the type parameters of a template into those of a template binding it -/

/-- The type parameters among the first `n` ones that `c` does *not* use: the *free* type
parameters. -/
def freeIdxs (c : TyConsId) (n : ℕ) : List TyIdx := (List.range n).filter (· ∉ c.params)

/-- The number of free type parameters. -/
def freeArity (c : TyConsId) (n : ℕ) : ℕ := (c.freeIdxs n).length

/-- The renaming embedding the `n` type parameters of a template producing `c` into the type
parameters of a template binding it: a type parameter `c` uses is sent to the type parameter
`osel` prescribes at its position, and the free ones to consecutive positions from `base`
on. -/
def mergeRen (c : TyConsId) (osel : List TyIdx) (base n : ℕ) : TyIdx → TyIdx := fun i =>
  if i ∈ c.params then osel.getD (c.params.idxOf i) 0 else base + (c.freeIdxs n).idxOf i

/-! ### Pinning a type parameter to a type constructor

Pinning a type parameter to a type constructor `τ` — a concrete type, or a constructor with
type parameters of its own, such as `List<T>` — is a substitution of *constructors* for type
parameters (`TyConsId.substCons`): the pinned parameter `i` becomes `τ`, whose type parameters
become new
type parameters placed — in order of first occurrence — *at* the position of the pinned one,
`i, i + 1, …, i + τ.arity - 1` (`TyConsId.shiftTo`), the type parameters before `i` stay where
they are and the ones after it move along to make room (`TyConsId.keptIdx`,
`TyConsId.specSubst`).  Pinning the type parameter of `List<T>` to `List<T>` thus gives
`List<List<T>>`, and pinning the first type parameter of `Pair<T₀, T₁>` to `List<T>` gives
`Pair<List<T₀>, T₁>`: a constructor in anonymous order stays in anonymous order
(`TyConsId.InAnonOrder.substCons_specSubst`). -/
mutual
/-- Substitute a type *constructor* for each type parameter of a type constructor. -/
def substCons (f : TyIdx → TyConsId) : TyConsId → TyConsId
  | .base kind => .base kind
  | .custom name args => .custom name (substConsList f args)
  | .param i => f i
/-- Substitute a type constructor for each type parameter of a list of type constructors. -/
def substConsList (f : TyIdx → TyConsId) : List TyConsId → List TyConsId
  | [] => []
  | c :: cs => substCons f c :: substConsList f cs
end

/-- The constructor `τ` with its type parameters renamed, in order of first occurrence, to
`base, base + 1, …, base + τ.arity - 1`: the anonymous form of `τ`, shifted to start at
`base`. -/
def shiftTo (τ : TyConsId) (base : ℕ) : TyConsId := τ.anon.rename (base + ·)

/-- The position of the `j`-th kept type parameter of a constructor whose type parameter `i`
is pinned to a constructor with `k` type parameters: the kept type parameters before `i` stay at
their position, and the ones after it come after the `k` type parameters of the pinned
constructor, which take up the positions `i, …, i + k - 1`. -/
def keptIdx (i k j : ℕ) : ℕ := if j < i then j else j + k

/-- The substitution pinning the type parameter `i` to the type constructor `τ`: the
parameter `i` becomes `τ`, whose own type parameters are placed from `i` on
(`TyConsId.shiftTo`), every earlier type parameter stays where it is and every later one moves
down one position among the kept ones, placed after those of `τ` (`TyConsId.keptIdx`). -/
def specSubst (i : TyIdx) (τ : TyConsId) : TyIdx → TyConsId := fun j =>
  if j = i then τ.shiftTo i else .param (keptIdx i τ.arity (if j < i then j else j - 1))

end TyConsId

/-! ## Properties -/

namespace TyArgs

variable {m n : ℕ}

@[simp] theorem get_ofList (l : List Ty) (i : TyIdx) :
    get (ofList l) i = l.getD i Ty.unit := by
  rw [get, TeleArg.toList_ofList]

/-- Reading a type argument off a tuple, by position in its list of types. -/
theorem get_eq_getElem {τs : TyArgs n} {i : TyIdx} (h : i < n) :
    get τs i = (TeleArg.toList τs)[i]'(by rw [TeleArg.toList_length]; exact h) := by
  rw [get, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [TeleArg.toList_length]; exact h), Option.getD_some]

/-- A type argument supplied for one of the `n` type parameters is one of the types of the
tuple. -/
theorem get_mem {τs : TyArgs n} {i : TyIdx} (h : i < n) : get τs i ∈ TeleArg.toList τs := by
  rw [get_eq_getElem h]
  exact List.getElem_mem _

/-- Two tuples with the same type arguments are the same tuple. -/
theorem ext {τs σs : TyArgs n} (h : ∀ i < n, get τs i = get σs i) : τs = σs := by
  refine TeleArg.toList_injective _ _ (List.ext_getElem (by simp) fun i hi hi' => ?_)
  rw [TeleArg.toList_length] at hi
  rw [← get_eq_getElem hi, ← get_eq_getElem hi, h i hi]

@[simp] theorem toList_transport (h : m = n) (τs : TyArgs m) :
    TeleArg.toList (transport h τs) = TeleArg.toList τs := TeleArg.toList_transport h τs

/-- Padding the list of types of a tuple to its own length recovers the tuple. -/
@[simp] theorem ofListPad_toList (τs : TyArgs n) : ofListPad n (TeleArg.toList τs) = τs :=
  TeleArg.toList_injective _ _ (TeleArg.toList_ofListPad _ (TeleArg.toList_length τs))

/-- The type arguments of a reindexed tuple (`TeleArg.reindex`): the type parameter `i` receives
the type argument `ρ i` of `τs`. -/
@[simp] theorem toList_reindex (ρ : TyIdx → TyIdx) (n : ℕ) (τs : TyArgs m) :
    TeleArg.toList (τs.reindex .unit ρ n) = (List.range n).map fun i => get τs (ρ i) :=
  TeleArg.toList_reindex _ _ _ _

@[simp] theorem get_reindex {ρ : TyIdx → TyIdx} {n : ℕ} {τs : TyArgs m} {i : TyIdx}
    (h : i < n) : get (τs.reindex .unit ρ n) i = get τs (ρ i) :=
  TeleArg.getD_toList_reindex _ _ _ h

/-- Every type argument of a reindexed tuple is a type argument of the original tuple. -/
theorem mem_toList_reindex {ρ : TyIdx → TyIdx} {n : ℕ} {τs : TyArgs m} {τ : Ty}
    (h : τ ∈ TeleArg.toList (τs.reindex .unit ρ n)) : ∃ i < n, τ = get τs (ρ i) := by
  rw [toList_reindex, List.mem_map] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, List.mem_range.mp hi, rfl⟩

/-- Reading a type argument off the first part of a split tuple. -/
theorem get_splitUniform_left {n m : ℕ} (types : TyArgs (n + m)) {i : TyIdx} (hi : i < n) :
    get (types.splitUniform n m).1 i = get types i :=
  TeleArg.getD_toList_splitUniform_left Ty.unit types hi

/-- Reading a type argument off the first part of a concatenation of tuples. -/
theorem get_appendUniform_left (a : TyArgs n) (b : TyArgs m) {i : TyIdx} (h : i < n) :
    get (a.appendUniform b) i = get a i := by
  have hlen : (TeleArg.toList a).length = n := TeleArg.toList_length a
  have hi : i < (TeleArg.toList a).length := by rw [hlen]; exact h
  rw [get, get, TeleArg.toList_appendUniform, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- Reading a type argument off the second part of a concatenation of tuples. -/
theorem get_appendUniform_right (a : TyArgs n) (b : TyArgs m) (j : TyIdx) :
    get (a.appendUniform b) (n + j) = get b j := by
  have hlen : (TeleArg.toList a).length = n := TeleArg.toList_length a
  have hi : (TeleArg.toList a).length ≤ n + j := by rw [hlen]; exact Nat.le_add_right _ _
  rw [get, get, TeleArg.toList_appendUniform, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_right hi, hlen,
    Nat.add_sub_cancel_left]

end TyArgs

namespace TyIdx

@[simp] theorem mem_dedup : ∀ {l : List TyIdx} {i : TyIdx}, i ∈ dedup l ↔ i ∈ l
  | [], _ => Iff.rfl
  | j :: l, i => by
      rw [dedup, List.mem_cons, List.mem_cons, List.mem_filter]
      constructor
      · rintro (rfl | ⟨h, -⟩)
        · exact Or.inl rfl
        · exact Or.inr (mem_dedup.mp h)
      · rintro (rfl | h)
        · exact Or.inl rfl
        · by_cases hij : i = j
          · exact Or.inl hij
          · exact Or.inr ⟨mem_dedup.mpr h, by simpa using hij⟩

theorem dedup_nodup : ∀ l : List TyIdx, (dedup l).Nodup
  | [] => List.nodup_nil
  | i :: l => by
      rw [dedup, List.nodup_cons]
      refine ⟨fun h => ?_, (dedup_nodup l).filter _⟩
      exact absurd (List.of_mem_filter h) (by simp)

/-! ### Positions in a list of indices

Taking positions in a list of indices is injective on the indices of the list, takes a list
without repetitions onto an initial segment of ℕ, and commutes with deduplication. -/

/-- Two indices at the same position in a list are the same index. -/
theorem eq_of_idxOf_eq {l : List TyIdx} {i j : TyIdx} (hi : i ∈ l) (hj : j ∈ l)
    (h : l.idxOf i = l.idxOf j) : i = j := by
  have hi' := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hi)
  have hj' := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hj)
  rw [← hi', ← hj']
  simp [h]

/-- Reading off the positions of the entries of a list without repetitions enumerates
them. -/
theorem map_idxOf_eq_range {l : List TyIdx} (h : l.Nodup) :
    l.map (fun i => l.idxOf i) = List.range l.length := by
  refine List.ext_getElem (by simp) fun k hk _ => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact h.idxOf_getElem k (by simpa using hk)

/-- An index below `n` is at its own position in `List.range n`. -/
theorem idxOf_range {n i : ℕ} (h : i < n) : (List.range n).idxOf i = i := by
  have h' := (List.nodup_range (n := n)).idxOf_getElem i (by simpa using h)
  simpa using h'

/-- Positions are preserved by a renaming injective on the list. -/
theorem idxOf_map_of_injOn {ρ : TyIdx → TyIdx} : ∀ {l : List TyIdx} {i : TyIdx}, i ∈ l →
    (∀ a ∈ l, ∀ b ∈ l, ρ a = ρ b → a = b) → (l.map ρ).idxOf (ρ i) = l.idxOf i
  | j :: l, i, hi, hinj => by
      by_cases hij : i = j
      · subst hij; simp
      · have hρ : ρ j ≠ ρ i := fun he => hij (hinj i (by simp [hi]) j (by simp) he.symm)
        have hi' : i ∈ l := (List.mem_cons.mp hi).resolve_left hij
        rw [List.map_cons, List.idxOf_cons_ne _ hρ, List.idxOf_cons_ne _ (Ne.symm hij),
          idxOf_map_of_injOn hi'
            (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb]))]

private theorem filter_ne_map {ρ : TyIdx → TyIdx} {i : TyIdx} : ∀ {m : List TyIdx},
    (∀ j ∈ m, ρ j = ρ i → j = i) →
      (m.map ρ).filter (fun x => decide (x ≠ ρ i))
        = (m.filter (fun x => decide (x ≠ i))).map ρ
  | [], _ => rfl
  | j :: m, h => by
      have ih := filter_ne_map (ρ := ρ) (i := i) (m := m)
        (fun k hk => h k (List.mem_cons_of_mem _ hk))
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      by_cases hj : j = i
      · subst hj
        simpa using ih
      · have hρ : ρ j ≠ ρ i := fun he => hj (h j (by simp) he)
        simp only [hj, hρ, ne_eq, decide_not, decide_false, Bool.not_false, if_true,
          List.map_cons, List.cons.injEq, true_and]
        simpa using ih

/-- Deduplication commutes with a renaming injective on the list. -/
theorem dedup_map {ρ : TyIdx → TyIdx} : ∀ {l : List TyIdx},
    (∀ i ∈ l, ∀ j ∈ l, ρ i = ρ j → i = j) → dedup (l.map ρ) = (dedup l).map ρ
  | [], _ => rfl
  | i :: l, h => by
      have ih := dedup_map (ρ := ρ) (l := l)
        (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      rw [List.map_cons, dedup, dedup, ih,
        filter_ne_map (fun j hj => h j (List.mem_cons_of_mem _ (mem_dedup.mp hj)) i (by simp)),
        List.map_cons]

/-- Deduplicating a list without repetitions leaves it unchanged. -/
theorem dedup_of_nodup : ∀ {l : List TyIdx}, l.Nodup → dedup l = l
  | [], _ => rfl
  | i :: l, h => by
      rw [List.nodup_cons] at h
      rw [dedup, dedup_of_nodup h.2, List.filter_eq_self.mpr fun j hj => by
        have : j ≠ i := fun hji => h.1 (hji ▸ hj)
        simpa using this]

/-- Deduplication commutes with filtering. -/
theorem dedup_filter (p : TyIdx → Bool) : ∀ l : List TyIdx,
    dedup (l.filter p) = (dedup l).filter p
  | [] => rfl
  | i :: l => by
      rw [dedup, List.filter_cons]
      split
      · rename_i hp
        rw [dedup, dedup_filter p l, List.filter_cons, if_pos hp, List.filter_filter,
          List.filter_filter]
        congr 2
        funext x
        rw [Bool.and_comm]
      · rename_i hp
        rw [dedup_filter p l, List.filter_cons, if_neg hp, List.filter_filter]
        congr 1
        funext x
        by_cases hx : x = i
        · subst hx; simp [hp]
        · simp [hx]

/-- Deduplicating a concatenation: the deduplicated first part, followed by the entries of the
deduplicated second part not in the first one. -/
theorem dedup_append : ∀ (l m : List TyIdx),
    dedup (l ++ m) = dedup l ++ (dedup m).filter (fun x => decide (x ∉ l))
  | [], m => by simp [dedup]
  | i :: l, m => by
      rw [List.cons_append, dedup, dedup, dedup_append l m, List.filter_append, List.cons_append,
        List.filter_filter]
      congr 2
      refine List.filter_congr fun x _ => ?_
      by_cases hx : x = i
      · subst hx; simp
      · simp [hx]

/-- Deduplicating a concatenation of blocks only depends on the first block of every index. -/
theorem dedup_flatMap (g : TyIdx → List TyIdx) : ∀ l : List TyIdx,
    dedup (l.flatMap g) = dedup ((dedup l).flatMap g)
  | [] => rfl
  | i :: l => by
      rw [List.flatMap_cons, dedup, List.flatMap_cons, dedup_append, dedup_append,
        dedup_flatMap g l]
      congr 1
      rw [← dedup_filter, ← dedup_filter]
      congr 1
      rw [List.filter_flatMap, List.filter_flatMap]
      generalize dedup l = L
      induction L with
      | nil => rfl
      | cons a L ih =>
        rw [List.flatMap_cons, List.filter_cons, ih]
        by_cases ha : a = i
        · subst ha
          rw [if_neg (by simp), List.filter_eq_nil_iff.mpr (fun x hx => by simpa using hx),
            List.nil_append]
        · rw [if_pos (by simpa using ha), List.flatMap_cons]

end TyIdx

namespace TyConsId

theorem idxsList_eq_flatten : ∀ cs : List TyConsId,
    idxsList cs = (cs.map idxs).flatten
  | [] => rfl
  | c :: cs => by rw [idxsList, List.map_cons, List.flatten_cons, idxsList_eq_flatten cs]

@[simp] theorem mem_params {c : TyConsId} {i : TyIdx} : i ∈ c.params ↔ i ∈ c.idxs :=
  TyIdx.mem_dedup

theorem params_nodup (c : TyConsId) : c.params.Nodup := TyIdx.dedup_nodup _

@[simp] theorem idxs_base (kind : BaseTy) : (TyConsId.base kind).idxs = [] := rfl
@[simp] theorem idxs_param (i : TyIdx) : (TyConsId.param i).idxs = [i] := rfl
@[simp] theorem idxs_custom (name : Tid) (args : List TyConsId) :
    (TyConsId.custom name args).idxs = (args.map idxs).flatten := idxsList_eq_flatten args
@[simp] theorem params_base (kind : BaseTy) : (TyConsId.base kind).params = [] := rfl
@[simp] theorem params_param (i : TyIdx) : (TyConsId.param i).params = [i] := rfl
@[simp] theorem arity_base (kind : BaseTy) : (TyConsId.base kind).arity = 0 := rfl
@[simp] theorem arity_param (i : TyIdx) : (TyConsId.param i).arity = 1 := rfl

/-- Every type parameter of an argument of a custom constructor is a type parameter of that
constructor. -/
theorem mem_idxs_custom {name : Tid} {args : List TyConsId} {a : TyConsId} (ha : a ∈ args)
    {i : TyIdx} (hi : i ∈ a.idxs) : i ∈ (TyConsId.custom name args).idxs := by
  rw [idxs_custom, List.mem_flatten]
  exact ⟨a.idxs, List.mem_map_of_mem ha, hi⟩

theorem renameList_eq_map (ρ : TyIdx → TyIdx) : ∀ cs : List TyConsId,
    renameList ρ cs = cs.map (rename ρ)
  | [] => rfl
  | c :: cs => by rw [renameList, List.map_cons, renameList_eq_map ρ cs]

@[simp] theorem rename_base (ρ : TyIdx → TyIdx) (kind : BaseTy) :
    (TyConsId.base kind).rename ρ = .base kind := rfl
@[simp] theorem rename_param (ρ : TyIdx → TyIdx) (i : TyIdx) :
    (TyConsId.param i).rename ρ = .param (ρ i) := rfl
@[simp] theorem rename_custom (ρ : TyIdx → TyIdx) (name : Tid) (args : List TyConsId) :
    (TyConsId.custom name args).rename ρ = .custom name (args.map (rename ρ)) := by
  rw [rename, renameList_eq_map]

theorem substList_eq_map (f : TyIdx → Ty) : ∀ cs : List TyConsId,
    substList f cs = cs.map (subst f)
  | [] => rfl
  | c :: cs => by rw [substList, List.map_cons, substList_eq_map f cs]

@[simp] theorem subst_base (f : TyIdx → Ty) (kind : BaseTy) :
    (TyConsId.base kind).subst f = .base kind := rfl
@[simp] theorem subst_param (f : TyIdx → Ty) (i : TyIdx) :
    (TyConsId.param i).subst f = f i := rfl
@[simp] theorem subst_custom (f : TyIdx → Ty) (name : Tid) (args : List TyConsId) :
    (TyConsId.custom name args).subst f = .custom name (args.map (subst f)) := by
  rw [subst, substList_eq_map]

@[simp] theorem concretise_base {n : ℕ} (kind : BaseTy) (τs : TyArgs n) :
    (TyConsId.base kind).concretise τs = .base kind := rfl
@[simp] theorem concretise_param {n : ℕ} (i : TyIdx) (τs : TyArgs n) :
    (TyConsId.param i).concretise τs = TyArgs.get τs i := rfl

/-! #### Instantiation and concretisation -/

/-- Concretising at the tuple of the list of types of a tuple is concretising at that
tuple. -/
@[simp] theorem concretise_ofList_toList {n : ℕ} (c : TyConsId) (τs : TyArgs n) :
    c.concretise (TyArgs.ofList (TeleArg.toList τs)) = c.concretise τs := by
  rw [concretise, concretise]
  congr 1
  funext i
  rw [TyArgs.get_ofList]
  rfl

/-- Instantiation succeeds when the constructor only uses type parameters within the list. -/
theorem instantiate_eq_some {c : TyConsId} {τs : List Ty} (h : c.Bounded τs.length) :
    c.instantiate τs = some (c.concretise (TyArgs.ofList τs)) := if_pos h
/-- Instantiation fails when the constructor uses a type parameter beyond the list. -/
theorem instantiate_eq_none {c : TyConsId} {τs : List Ty} (h : ¬ c.Bounded τs.length) :
    c.instantiate τs = none := if_neg h
/-- Instantiation succeeds only when the constructor uses no type parameter beyond the
list. -/
theorem bounded_of_instantiate {c : TyConsId} {τs : List Ty} {τ : Ty}
    (h : c.instantiate τs = some τ) : c.Bounded τs.length := by
  by_contra hne
  rw [instantiate_eq_none hne] at h
  cases h
/-- A successful instantiation is the concretisation at the tuple of those types. -/
theorem eq_concretise_of_instantiate {c : TyConsId} {τs : List Ty} {τ : Ty}
    (h : c.instantiate τs = some τ) :
    c.Bounded τs.length ∧ τ = c.concretise (TyArgs.ofList τs) := by
  have hb := bounded_of_instantiate h
  rw [instantiate_eq_some hb] at h
  exact ⟨hb, (Option.some.inj h).symm⟩
/-- **Instantiating a bounded constructor at the list of a tuple of type arguments is
concretising it at that tuple.** -/
theorem instantiate_toList {c : TyConsId} {n : ℕ} (h : c.Bounded n) (τs : TyArgs n) :
    c.instantiate (TeleArg.toList τs) = some (c.concretise τs) := by
  rw [instantiate_eq_some (by rw [TeleArg.toList_length]; exact h), concretise_ofList_toList]
/-- The type a bounded constructor instantiates to at the list of a tuple of type arguments,
with any fallback, is its concretisation at that tuple. -/
theorem instantiate_toList_getD {c : TyConsId} {n : ℕ} (h : c.Bounded n) (τs : TyArgs n)
    (τ : Ty) : (c.instantiate (TeleArg.toList τs)).getD τ = c.concretise τs := by
  rw [instantiate_toList h, Option.getD_some]

/-- Renaming only depends on the type parameters the constructor uses. -/
theorem rename_congr {ρ σ : TyIdx → TyIdx} :
    ∀ (c : TyConsId), (∀ i ∈ c.params, ρ i = σ i) → c.rename ρ = c.rename σ := by
  refine TyConsId.ind' (fun _ _ => rfl) (fun i h => ?_) (fun name args ih h => ?_)
  · rw [rename_param, rename_param, h i (by simp)]
  · rw [rename_custom, rename_custom]
    refine congrArg _ (List.map_congr_left fun a ha => ih a ha fun i hi => ?_)
    exact h i (mem_params.mpr (mem_idxs_custom ha (mem_params.mp hi)))

/-- Substitution only depends on the type parameters the constructor uses. -/
theorem subst_congr {f g : TyIdx → Ty} :
    ∀ (c : TyConsId), (∀ i ∈ c.params, f i = g i) → c.subst f = c.subst g := by
  refine TyConsId.ind' (fun _ _ => rfl) (fun i h => ?_) (fun name args ih h => ?_)
  · rw [subst_param, subst_param, h i (by simp)]
  · rw [subst_custom, subst_custom]
    refine congrArg _ (List.map_congr_left fun a ha => ih a ha fun i hi => ?_)
    exact h i (mem_params.mpr (mem_idxs_custom ha (mem_params.mp hi)))

@[simp] theorem rename_id : ∀ c : TyConsId, c.rename (fun i => i) = c := by
  refine TyConsId.ind' (fun _ => rfl) (fun _ => rfl) (fun name args ih => ?_)
  rw [rename_custom]
  exact congrArg _ (by rw [List.map_congr_left ih]; simp)

theorem rename_rename (ρ σ : TyIdx → TyIdx) :
    ∀ c : TyConsId, (c.rename ρ).rename σ = c.rename (σ ∘ ρ) := by
  refine TyConsId.ind' (fun _ => rfl) (fun _ => rfl) (fun name args ih => ?_)
  rw [rename_custom, rename_custom, rename_custom, List.map_map]
  exact congrArg _ (List.map_congr_left ih)

theorem subst_rename (f : TyIdx → Ty) (ρ : TyIdx → TyIdx) :
    ∀ c : TyConsId, (c.rename ρ).subst f = c.subst (f ∘ ρ) := by
  refine TyConsId.ind' (fun _ => rfl) (fun _ => rfl) (fun name args ih => ?_)
  rw [rename_custom, subst_custom, subst_custom, List.map_map]
  exact congrArg _ (List.map_congr_left ih)

theorem idxs_rename (ρ : TyIdx → TyIdx) :
    ∀ c : TyConsId, (c.rename ρ).idxs = c.idxs.map ρ := by
  refine TyConsId.ind' (fun _ => rfl) (fun _ => rfl) (fun name args ih => ?_)
  rw [rename_custom, idxs_custom, idxs_custom, List.map_map, List.map_flatten, List.map_map]
  exact congrArg _ (List.map_congr_left fun a ha => ih a ha)

theorem mem_params_rename {ρ : TyIdx → TyIdx} {c : TyConsId} {j : TyIdx}
    (h : j ∈ (c.rename ρ).params) : ∃ i ∈ c.params, j = ρ i := by
  rw [mem_params, idxs_rename, List.mem_map] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, mem_params.mpr hi, rfl⟩

/-- A renamed constructor is bounded as soon as the renaming stays below the bound. -/
theorem Bounded.rename {c : TyConsId} {ρ : TyIdx → TyIdx} {n : ℕ}
    (h : ∀ i ∈ c.params, ρ i < n) : (c.rename ρ).Bounded n := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := mem_params_rename hj
  exact h i hi

/-- Instantiating a bounded constructor at a reindexed tuple is instantiating the renamed
constructor. -/
theorem concretise_reindex {n m : ℕ} (c : TyConsId) (ρ : TyIdx → TyIdx) (τs : TyArgs m)
    (h : c.Bounded n) :
    c.concretise (TeleArg.reindex Ty.unit ρ n τs) = (c.rename ρ).concretise τs := by
  rw [concretise, concretise, subst_rename]
  exact subst_congr c fun i hi => TyArgs.get_reindex (h i hi)

/-- A constructor using only the first `n` type parameters is instantiated by the first part
of a split tuple exactly as by the whole tuple. -/
theorem concretise_splitUniform_left {n m : ℕ} {c : TyConsId} (h : c.Bounded n)
    (types : TyArgs (n + m)) :
    c.concretise (types.splitUniform n m).1 = c.concretise types :=
  subst_congr c fun i hi => TyArgs.get_splitUniform_left types (h i hi)

/-! ### The type constructor of a concrete type -/

@[simp] theorem idxs_consId : ∀ τ : Ty, (Ty.consId τ).idxs = []
  | .base _ => rfl
  | .custom _ τs => by
      rw [Ty.consId_custom, idxs_custom, List.map_map]
      refine List.flatten_eq_nil_iff.mpr fun l hl => ?_
      obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hl
      exact idxs_consId τ

@[simp] theorem params_consId (τ : Ty) : (Ty.consId τ).params = [] := by
  rw [params, idxs_consId]; rfl

@[simp] theorem subst_consId (f : TyIdx → Ty) : ∀ τ : Ty, (Ty.consId τ).subst f = τ
  | .base _ => rfl
  | .custom name τs => by
      rw [Ty.consId_custom, subst_custom, List.map_map]
      refine congrArg _ ?_
      simp only [Function.comp_def]
      rw [List.map_congr_left (g := fun τ => τ) fun τ _ => subst_consId f τ]
      simp

@[simp] theorem concretise_consId {n : ℕ} (τ : Ty) (τs : TyArgs n) :
    (Ty.consId τ).concretise τs = τ := subst_consId _ τ

/-- The type parameters of a renamed constructor are the renamed type parameters, as soon as
the renaming is injective on them. -/
theorem params_rename_of_injOn {c : TyConsId} {ρ : TyIdx → TyIdx}
    (h : ∀ i ∈ c.params, ∀ j ∈ c.params, ρ i = ρ j → i = j) :
    (c.rename ρ).params = c.params.map ρ := by
  rw [params, idxs_rename,
    TyIdx.dedup_map (fun i hi j hj => h i (mem_params.mpr hi) j (mem_params.mpr hj))]
  rfl

theorem anonRen_apply (c : TyConsId) (i : TyIdx) : c.anonRen i = c.params.idxOf i := rfl

/-- The canonical renaming is injective on the type parameters it renames. -/
theorem anonRen_injOn (c : TyConsId) :
    ∀ i ∈ c.params, ∀ j ∈ c.params, c.anonRen i = c.anonRen j → i = j :=
  fun _ hi _ hj h => TyIdx.eq_of_idxOf_eq hi hj h

/-- An anonymous constructor uses exactly the type parameters `0, …, arity - 1`. -/
@[simp] theorem params_anon (c : TyConsId) : c.anon.params = List.range c.arity := by
  rw [anon, params_rename_of_injOn (anonRen_injOn c), arity]
  exact TyIdx.map_idxOf_eq_range (params_nodup c)

/-- Anonymising a constructor does not change how many type parameters it uses. -/
@[simp] theorem arity_anon (c : TyConsId) : c.anon.arity = c.arity := by
  rw [arity, params_anon, List.length_range]

/-- An anonymous constructor only uses type parameters below its arity. -/
theorem anon_bounded (c : TyConsId) : c.anon.Bounded c.arity := by
  intro i hi
  rw [params_anon, List.mem_range] at hi
  exact hi

/-- The anonymous form is canonical: anonymising it again changes nothing. -/
@[simp] theorem anon_anon (c : TyConsId) : c.anon.anon = c.anon := by
  refine Eq.trans (rename_congr (ρ := c.anon.anonRen) (σ := fun i => i) c.anon ?_) (rename_id _)
  intro i hi
  rw [anonRen_apply, params_anon] at *
  exact TyIdx.idxOf_range (List.mem_range.mp hi)

@[simp] theorem anon_base (kind : BaseTy) : (TyConsId.base kind).anon = .base kind := rfl

@[simp] theorem anon_param (i : TyIdx) : (TyConsId.param i).anon = .param 0 := by
  simp [anon, anonRen]

/-- Renaming the type parameters of a constructor injectively does not change its anonymous
form. -/
theorem anon_rename_of_injOn {c : TyConsId} {ρ : TyIdx → TyIdx}
    (h : ∀ i ∈ c.params, ∀ j ∈ c.params, ρ i = ρ j → i = j) : (c.rename ρ).anon = c.anon := by
  rw [anon, anon, rename_rename]
  refine rename_congr c fun i hi => ?_
  simp only [Function.comp_apply, anonRen_apply, params_rename_of_injOn h]
  exact TyIdx.idxOf_map_of_injOn hi h

/-- A type parameter is at its own position in the list of type parameters. -/
theorem getD_idxOf_params {c : TyConsId} {i : TyIdx} (h : i ∈ c.params) :
    c.params.getD (c.params.idxOf i) 0 = i := by
  have hlt : c.params.idxOf i < c.params.length := List.idxOf_lt_length_iff.mpr h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact List.getElem_idxOf hlt

@[refl] theorem Match.refl (c : TyConsId) : c.Match c := rfl

theorem Match.symm {c C : TyConsId} (h : c.Match C) : C.Match c := Eq.symm h

theorem Match.trans {c C D : TyConsId} (h : c.Match C) (h' : C.Match D) : c.Match D :=
  Eq.trans h h'

/-- A constructor matches its own anonymous form. -/
theorem match_anon (c : TyConsId) : c.Match c.anon := (anon_anon c).symm

/-- An injective renaming of the type parameters produces a matching constructor: *any*
renaming of the type parameters is a valid match. -/
theorem match_rename {c : TyConsId} {ρ : TyIdx → TyIdx}
    (h : ∀ i ∈ c.params, ∀ j ∈ c.params, ρ i = ρ j → i = j) : (c.rename ρ).Match c :=
  anon_rename_of_injOn h

/-- Matching constructors are related by the transfer renaming: renaming the type parameters
of one of them position by position produces the other. -/
theorem Match.rename_transfer {c C : TyConsId} (h : c.Match C) :
    c.rename (c.transfer C) = C := by
  have key : c.transfer C = (fun k => C.params.getD k 0) ∘ c.anonRen := rfl
  rw [key, ← rename_rename, show c.rename c.anonRen = c.anon from rfl, h,
    show C.anon = C.rename C.anonRen from rfl, rename_rename]
  exact Eq.trans (rename_congr (σ := fun i => i) C fun i hi => getD_idxOf_params hi)
    (rename_id _)

/-- Matching constructors use the same number of type parameters. -/
theorem Match.arity_eq {c C : TyConsId} (h : c.Match C) : c.arity = C.arity := by
  rw [← arity_anon c, ← arity_anon C, h]

theorem mem_freeIdxs {c : TyConsId} {n : ℕ} {i : TyIdx} :
    i ∈ c.freeIdxs n ↔ i < n ∧ i ∉ c.params := by
  rw [freeIdxs, List.mem_filter, List.mem_range]
  simp

theorem freeIdxs_nodup (c : TyConsId) (n : ℕ) : (c.freeIdxs n).Nodup :=
  (List.nodup_range).filter _

theorem mergeRen_of_mem {c : TyConsId} {osel : List TyIdx} {base n : ℕ} {i : TyIdx}
    (h : i ∈ c.params) : c.mergeRen osel base n i = osel.getD (c.params.idxOf i) 0 :=
  if_pos h

theorem mergeRen_of_notMem {c : TyConsId} {osel : List TyIdx} {base n : ℕ} {i : TyIdx}
    (h : i ∉ c.params) : c.mergeRen osel base n i = base + (c.freeIdxs n).idxOf i :=
  if_neg h

/-- On the type parameters it uses, the embedding `mergeRen` at the type parameters of `C` is
the transfer renaming to `C`. -/
theorem mergeRen_eq_transfer {c C : TyConsId} {base n : ℕ} {i : TyIdx} (h : i ∈ c.params) :
    c.mergeRen C.params base n i = c.transfer C i := mergeRen_of_mem h

/-- Embedding a constructor at the type parameters of a matching one gives that
constructor. -/
theorem rename_mergeRen {c C : TyConsId} (h : c.Match C) (base n : ℕ) :
    c.rename (c.mergeRen C.params base n) = C := by
  rw [rename_congr c (σ := c.transfer C) fun i hi => mergeRen_eq_transfer hi]
  exact h.rename_transfer

/-- A used type parameter is embedded among the type parameters prescribed by `osel`. -/
theorem mergeRen_lt_of_mem {c : TyConsId} {osel : List TyIdx} {base n k : ℕ}
    (hosel : ∀ j ∈ osel, j < k) (hlen : c.arity ≤ osel.length) {i : TyIdx}
    (hi : i ∈ c.params) : c.mergeRen osel base n i < k := by
  have hlt : c.params.idxOf i < osel.length := by
    have := List.idxOf_lt_length_iff.mpr hi
    rw [arity] at hlen
    omega
  rw [mergeRen_of_mem hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
    Option.getD_some]
  exact hosel _ (List.getElem_mem hlt)

/-- A free type parameter is embedded among the fresh positions the template reserves for
it. -/
theorem mergeRen_free_lt {c : TyConsId} {osel : List TyIdx} {base n : ℕ} {i : TyIdx}
    (hi : i ∈ c.freeIdxs n) :
    base ≤ c.mergeRen osel base n i ∧ c.mergeRen osel base n i < base + c.freeArity n := by
  rw [mergeRen_of_notMem (mem_freeIdxs.mp hi).2]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (List.idxOf_lt_length_iff.mpr hi) base⟩

/-- The embedding of a source into the type parameters of the template binding it stays
below the arity of that template. -/
theorem mergeRen_lt {c : TyConsId} {osel : List TyIdx} {base n k : ℕ}
    (hosel : ∀ j ∈ osel, j < k) (hlen : c.arity ≤ osel.length) (hbase : k ≤ base)
    {i : TyIdx} (hi : i < n) :
    c.mergeRen osel base n i < base + c.freeArity n := by
  by_cases hmem : i ∈ c.params
  · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (mergeRen_lt_of_mem hosel hlen hmem) hbase)
      (Nat.le_add_right _ _)
  · exact (mergeRen_free_lt (mem_freeIdxs.mpr ⟨hi, hmem⟩)).2

/-- Distinct free type parameters are embedded at distinct positions. -/
theorem mergeRen_free_injective {c : TyConsId} {osel : List TyIdx} {base n : ℕ}
    {i j : TyIdx} (hi : i ∈ c.freeIdxs n) (hj : j ∈ c.freeIdxs n)
    (h : c.mergeRen osel base n i = c.mergeRen osel base n j) : i = j := by
  rw [mergeRen_of_notMem (mem_freeIdxs.mp hi).2, mergeRen_of_notMem (mem_freeIdxs.mp hj).2]
    at h
  have hi' : (c.freeIdxs n)[(c.freeIdxs n).idxOf i]'(List.idxOf_lt_length_iff.mpr hi) = i :=
    List.getElem_idxOf _
  have hj' : (c.freeIdxs n)[(c.freeIdxs n).idxOf j]'(List.idxOf_lt_length_iff.mpr hj) = j :=
    List.getElem_idxOf _
  have hidx : (c.freeIdxs n).idxOf i = (c.freeIdxs n).idxOf j := Nat.add_left_cancel h
  rw [← hi', ← hj']
  simp [hidx]

theorem substConsList_eq_map (f : TyIdx → TyConsId) : ∀ cs : List TyConsId,
    substConsList f cs = cs.map (substCons f)
  | [] => rfl
  | c :: cs => by rw [substConsList, List.map_cons, substConsList_eq_map f cs]

@[simp] theorem substCons_base (f : TyIdx → TyConsId) (kind : BaseTy) :
    (TyConsId.base kind).substCons f = .base kind := rfl
@[simp] theorem substCons_param (f : TyIdx → TyConsId) (i : TyIdx) :
    (TyConsId.param i).substCons f = f i := rfl
@[simp] theorem substCons_custom (f : TyIdx → TyConsId) (name : Tid) (args : List TyConsId) :
    (TyConsId.custom name args).substCons f = .custom name (args.map (substCons f)) := by
  rw [substCons, substConsList_eq_map]

mutual
/-- Substituting type constructors and then types is substituting the composite. -/
theorem subst_substCons (f : TyIdx → TyConsId) (g : TyIdx → Ty) :
    ∀ c : TyConsId, (c.substCons f).subst g = c.subst fun i => (f i).subst g
  | .base _ => rfl
  | .param _ => rfl
  | .custom name args => by
      rw [substCons, subst, subst, substList_substCons f g args]
theorem substList_substCons (f : TyIdx → TyConsId) (g : TyIdx → Ty) :
    ∀ cs : List TyConsId,
      substList g (substConsList f cs) = substList (fun i => (f i).subst g) cs
  | [] => rfl
  | c :: cs => by
      rw [substConsList, substList, substList, subst_substCons f g c,
        substList_substCons f g cs]
end

/-- The type parameters a substituted constructor uses come from the substituted
constructors. -/
theorem mem_idxs_substCons {f : TyIdx → TyConsId} {j : TyIdx} :
    ∀ (c : TyConsId), j ∈ (c.substCons f).idxs → ∃ k ∈ c.idxs, j ∈ (f k).idxs := by
  intro c
  induction c using TyConsId.ind' with
  | base kind => intro h; exact absurd h (by simp)
  | param i => intro h; exact ⟨i, by simp, h⟩
  | custom name args ih =>
    intro h
    rw [substCons_custom, idxs_custom, List.mem_flatten] at h
    obtain ⟨l, hl, hj⟩ := h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    obtain ⟨k, hk, hjk⟩ := ih a ha hj
    exact ⟨k, mem_idxs_custom ha hk, hjk⟩

/-! ### Shifting and pinning -/

/-- The type parameters of a shifted constructor are `base, …, base + τ.arity - 1`, in
order. -/
theorem params_shiftTo (τ : TyConsId) (base : ℕ) :
    (τ.shiftTo base).params = (List.range τ.arity).map (base + ·) := by
  rw [shiftTo, params_rename_of_injOn (fun i _ j _ h => Nat.add_left_cancel h), params_anon]

/-- A shifted constructor uses as many type parameters as the constructor itself. -/
@[simp] theorem arity_shiftTo (τ : TyConsId) (base : ℕ) : (τ.shiftTo base).arity = τ.arity := by
  rw [arity, params_shiftTo, List.length_map, List.length_range]

theorem mem_params_shiftTo {τ : TyConsId} {base j : ℕ} :
    j ∈ (τ.shiftTo base).params ↔ base ≤ j ∧ j < base + τ.arity := by
  rw [params_shiftTo, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [List.mem_range] at hk
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨j - base, List.mem_range.mpr (by omega), by omega⟩

/-- A shifted constructor only uses the type parameters reserved for it. -/
theorem shiftTo_bounded (τ : TyConsId) (base : ℕ) : (τ.shiftTo base).Bounded (base + τ.arity) :=
  fun _ hj => (mem_params_shiftTo.mp hj).2

/-- A shifted constructor matches the constructor itself: only the names of the type
parameters differ. -/
theorem shiftTo_match (τ : TyConsId) (base : ℕ) : (τ.shiftTo base).Match τ :=
  (anon_rename_of_injOn (c := τ.anon) (fun _ _ _ _ h => Nat.add_left_cancel h)).trans
    (anon_anon τ)

/-- The shift of the constructor of a concrete type is that constructor. -/
@[simp] theorem shiftTo_consId (τ : Ty) (base : ℕ) : (Ty.consId τ).shiftTo base = τ.consId := by
  have hself : ∀ d : TyConsId, d.params = [] → ∀ ρ : TyIdx → TyIdx, d.rename ρ = d := by
    intro d hd ρ
    refine Eq.trans (TyConsId.rename_congr (σ := fun j => j) d ?_) (TyConsId.rename_id d)
    intro j hj
    rw [hd] at hj
    cases hj
  rw [shiftTo, anon, hself _ (params_consId τ), hself _ (params_consId τ)]

private theorem specSubst_lt_aux {i k n : ℕ} (hkn : k < n) (hin : i < n) (hne : ¬ k = i) :
    (if k < i then k else k - 1) < n - 1 := by
  split <;> omega

/-- A kept type parameter is placed below the type parameters kept followed by those of the
pinned constructor. -/
theorem keptIdx_lt {i k j n : ℕ} (hj : j < n) : keptIdx i k j < n + k := by
  unfold keptIdx; split <;> omega

/-- Distinct kept type parameters are placed at distinct positions. -/
theorem keptIdx_inj {i k a b : ℕ} (h : keptIdx i k a = keptIdx i k b) : a = b := by
  unfold keptIdx at h; split_ifs at h <;> omega

/-- A kept type parameter is not placed among the type parameters of the pinned
constructor. -/
theorem keptIdx_notMem_pinned {i k j : ℕ} : ¬ (i ≤ keptIdx i k j ∧ keptIdx i k j < i + k) := by
  unfold keptIdx; split <;> omega

/-- Pinning a type parameter of a bounded constructor to `τ` leaves it bounded by the type
parameters kept, together with those of `τ`. -/
theorem Bounded.specSubst {c : TyConsId} {i : TyIdx} {n : ℕ} {τ : TyConsId}
    (h : c.Bounded n) (hi : i < n) :
    (c.substCons (TyConsId.specSubst i τ)).Bounded (n - 1 + τ.arity) := by
  intro j hj
  obtain ⟨k, hk, hjk⟩ := mem_idxs_substCons c (mem_params.mp hj)
  have hkn : k < n := h k (mem_params.mpr hk)
  rw [TyConsId.specSubst] at hjk
  by_cases hki : k = i
  · rw [if_pos hki] at hjk
    exact Nat.lt_of_lt_of_le (shiftTo_bounded τ i j (mem_params.mpr hjk))
      (Nat.add_le_add_right (Nat.le_sub_one_of_lt hi) _)
  · rw [if_neg hki, idxs_param, List.mem_singleton] at hjk
    subst hjk
    exact keptIdx_lt (specSubst_lt_aux hkn hi hki)

/-- Instantiating a constructor whose type parameter `i` is pinned to `τ`: it is the original
constructor instantiated at the tuple of the type arguments kept — read off the type arguments
before position `i` and after the `τ.arity` ones of `τ` (`TyConsId.keptIdx`) — with `τ`,
instantiated at the type arguments from position `i` on, inserted at position `i`. -/
theorem concretise_substCons_specSubst {c : TyConsId} {n : ℕ} (hc : c.Bounded n)
    {i : TyIdx} (hi : i < n) (τ : TyConsId) {M : ℕ} (types : TyArgs M) :
    (c.substCons (TyConsId.specSubst i τ)).concretise types
      = c.concretise (TeleArg.insertUniformPred ((τ.shiftTo i).concretise types) i (n := n)
          (TeleArg.reindex Ty.unit (keptIdx i τ.arity) (n - 1) types)) := by
  rw [concretise, concretise, subst_substCons]
  refine (subst_congr c fun j hj => ?_).symm
  have hjn : j < n := hc j hj
  show TyArgs.get _ j = _
  rw [TyArgs.get, TeleArg.getD_toList_insertUniformPred _ Ty.unit i hi _ j,
    TyConsId.specSubst]
  by_cases hji : j = i
  · rw [if_pos hji, if_pos hji]
    rfl
  · rw [if_neg hji, if_neg hji, subst_param]
    have hlt := specSubst_lt_aux hjn hi hji
    rw [← TyArgs.get, TyArgs.get_reindex hlt]

/-- Pinning the type parameter of `List<T>` to `List<T>` gives `List<List<T>>`. -/
theorem specSubst_list_list :
    (TyConsId.custom "List" [.param 0]).substCons
        (TyConsId.specSubst 0 (.custom "List" [.param 0]))
      = .custom "List" [.custom "List" [.param 0]] := by decide

/-- Pinning the first type parameter of `Pair<T₀, T₁>` to `List<U>` gives
`Pair<List<T₀>, T₁>`: the parameter of the pinned constructor — whatever its name — takes the
place of the pinned one, at `T₀`, and the kept parameter `T₁` stays after it. -/
theorem specSubst_pair_list :
    (TyConsId.custom "Pair" [.param 0, .param 1]).substCons
        (TyConsId.specSubst 0 (.custom "List" [.param 5]))
      = .custom "Pair" [.custom "List" [.param 0], .param 1] := by decide

/-! ### Pinning preserves the anonymous order -/

/-- The type parameters a substituted constructor uses, with repetitions: those of the
constructors substituted for its own, in order. -/
theorem idxs_substCons (f : TyIdx → TyConsId) :
    ∀ c : TyConsId, (c.substCons f).idxs = c.idxs.flatMap fun k => (f k).idxs := by
  intro c
  induction c using TyConsId.ind' with
  | base kind => rfl
  | param i => simp
  | custom name args ih =>
    rw [substCons_custom, idxs_custom, idxs_custom, List.map_map]
    induction args with
    | nil => rfl
    | cons a as iha =>
      rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons, List.flatMap_append,
        Function.comp_apply, ih a List.mem_cons_self,
        iha fun b hb => ih b (List.mem_cons_of_mem _ hb)]

/-- A constructor is in anonymous order exactly when the type parameters it uses are an initial
segment of the indices, in increasing order. -/
theorem inAnonOrder_iff {c : TyConsId} : c.InAnonOrder ↔ ∃ m, c.params = List.range m := by
  refine ⟨fun h => ⟨_, h⟩, fun ⟨m, hm⟩ => ?_⟩
  rw [InAnonOrder, arity, hm, List.length_range]

/-- The type parameters used by the constructors substituted for type parameters other than
the pinned one: the kept type parameters, at their new positions. -/
private theorem flatMap_specSubst_kept {i : ℕ} {τ : TyConsId} : ∀ l : List ℕ,
    (∀ j ∈ l, j ≠ i) →
      l.flatMap (fun k => (TyConsId.specSubst i τ k).idxs)
        = l.map fun j => keptIdx i τ.arity (if j < i then j else j - 1)
  | [], _ => rfl
  | a :: l, hl => by
      rw [List.flatMap_cons, List.map_cons, TyConsId.specSubst, if_neg (hl a List.mem_cons_self),
        idxs_param, List.singleton_append,
        flatMap_specSubst_kept l fun j hj => hl j (List.mem_cons_of_mem _ hj)]

/-- The type parameters used by the constructors substituted for the type parameters
`0, …, n - 1`, when the pinned one `i` is among them: the type parameters before `i`, those of
the pinned constructor, and the remaining kept ones, after those. -/
private theorem flatMap_specSubst_range {i n : ℕ} (τ : TyConsId) (hin : i < n) :
    (List.range n).flatMap (fun k => (TyConsId.specSubst i τ k).idxs)
      = List.range i ++ ((τ.shiftTo i).idxs ++ (List.range (n - 1 - i)).map (i + τ.arity + ·)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = i + 1 + m := ⟨n - i - 1, by omega⟩
  rw [show i + 1 + m - 1 - i = m by omega, List.range_add, List.range_succ, List.flatMap_append,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    flatMap_specSubst_kept _ fun j hj => by rw [List.mem_range] at hj; omega,
    flatMap_specSubst_kept _ fun j hj => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hj
      omega,
    TyConsId.specSubst, if_pos rfl, List.map_map, List.append_assoc]
  congr 1
  · conv_rhs => rw [← List.map_id (List.range i)]
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp [keptIdx, hj]
  · congr 1
    refine List.map_congr_left fun j _ => ?_
    have h1 : ¬ (i + 1 + j < i) := by omega
    have h2 : ¬ (i + 1 + j - 1 < i) := by omega
    simp only [Function.comp_apply, keptIdx, if_neg h1, if_neg h2]
    omega

/-- **Pinning preserves the anonymous order**: pinning a type parameter `i` of a constructor in
anonymous order to any `τ` gives a constructor in anonymous order, since the type parameters
of `τ` are placed at the position of the pinned one, in order of first occurrence. -/
theorem InAnonOrder.substCons_specSubst {c : TyConsId} (hc : c.InAnonOrder) (i : ℕ)
    (τ : TyConsId) : (c.substCons (TyConsId.specSubst i τ)).InAnonOrder := by
  rw [inAnonOrder_iff]
  have hrange : TyIdx.dedup c.idxs = List.range c.arity := hc
  rw [params, idxs_substCons, TyIdx.dedup_flatMap, hrange]
  generalize c.arity = n
  by_cases hin : i < n
  · refine ⟨n - 1 + τ.arity, ?_⟩
    have hBp : TyIdx.dedup (τ.shiftTo i).idxs = (List.range τ.arity).map (i + ·) :=
      params_shiftTo τ i
    rw [flatMap_specSubst_range τ hin, TyIdx.dedup_append,
      TyIdx.dedup_of_nodup List.nodup_range, TyIdx.dedup_append,
      TyIdx.dedup_of_nodup (List.nodup_range.map fun a b h => by simpa using h), hBp]
    have hC : ((List.range (n - 1 - i)).map (i + τ.arity + ·)).filter
        (fun x => decide (x ∉ (τ.shiftTo i).idxs)) = (List.range (n - 1 - i)).map (i + τ.arity + ·) := by
      refine List.filter_eq_self.mpr fun x hx => ?_
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      have : ¬ (i + τ.arity + y) ∈ (τ.shiftTo i).idxs := fun h' => by
        have := (mem_params_shiftTo.mp (mem_params.mpr h')).2
        omega
      simpa using this
    rw [hC]
    have hAB : ((List.range τ.arity).map (i + ·) ++ (List.range (n - 1 - i)).map (i + τ.arity + ·)).filter
        (fun x => decide (x ∉ List.range i))
        = (List.range τ.arity).map (i + ·) ++ (List.range (n - 1 - i)).map (i + τ.arity + ·) := by
      refine List.filter_eq_self.mpr fun x hx => ?_
      have : x ∉ List.range i := by
        rcases List.mem_append.mp hx with hx | hx <;> obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx <;>
          simp only [List.mem_range, not_lt] <;> omega
      simpa using this
    rw [hAB, show n - 1 + τ.arity = i + (τ.arity + (n - 1 - i)) by omega, List.range_add,
      List.range_add, List.map_append, List.map_map]
    congr 2
    exact List.map_congr_left fun j _ => by simp [Nat.add_assoc]
  · refine ⟨n, ?_⟩
    have hid : (List.range n).map (fun j => keptIdx i τ.arity (if j < i then j else j - 1))
        = List.range n := by
      conv_rhs => rw [← List.map_id (List.range n)]
      refine List.map_congr_left fun j hj => ?_
      rw [List.mem_range] at hj
      have hji : j < i := by omega
      simp [keptIdx, hji]
    rw [flatMap_specSubst_kept _ fun j hj => by rw [List.mem_range] at hj; omega, hid,
      TyIdx.dedup_of_nodup List.nodup_range]

end TyConsId

end RUXt
