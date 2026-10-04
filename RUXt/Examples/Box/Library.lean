import RUXt.Semantics.Inadequacy
import RUXt.Examples.Calls

namespace RUXt

open scoped PFun

universe u

/-!
# The `Box` library and its type unsoundness

A small (unsound) generic Rust-like library of boxes, together with the heap lemmas and the
RISL derivation shared by its functions.

The library exports four `safe` functions:

* `box<T>(x : T) -> Box<T>` allocates a memory cell and stores `x` in it;
* `rebox<T>(x : Box<T>) -> Box<T>` adds one more level of indirection by allocating a new
  cell holding the input box — but *declares* its result at type `Box<T>` again, which is
  the type-level lie the refutation exploits;
* `cycle<T>(x : Box<T>) -> Box<T>` overwrites the value the box holds with the head pointer
  itself, so that the head cell points at itself;
* `drop<T>(x : Box<T>) -> Unit` is the (recursive, and *generic*) drop glue: it reads the
  value a box holds and, unless that value is the unit value, frees the cell and drops the
  pointer it read in turn, at the very same type parameter `T`.

Running `box`, `rebox`, `cycle` and then `drop` exhibits a use-after-free.
-/

/-- The generic custom type `Box<T>`, as a type constructor: `Box` applied to the type
parameter of index `0`. -/
abbrev TyConsId.boxT : TyConsId := .custom "Box" [.param 0]

/-- `box<T>(x : T) -> Box<T>`: `let l = alloc 1 in let _ = store l x in l`. -/
abbrev boxBody : Expr :=
  .letIn (.named "l") (.alloc (.int 1))
    (.letIn .anon (.store (.var "l") (.var "x")) (.var "l"))
def boxDecl : FunDecl := ⟨1, ⟨[("x", .param 0)], fun _ => boxBody, .boxT, true⟩⟩
def boxImpl (τ : Ty) : FunImpl := boxDecl.concretise ⟨τ, PUnit.unit⟩

/-- `rebox<T>(x : Box<T>) -> Box<T>`: the same body as `box`, so the result really is a
`Box<Box<T>>`, but the declared result type is `Box<T>`. -/
abbrev reboxBody : Expr :=
  .letIn (.named "l") (.alloc (.int 1))
    (.letIn .anon (.store (.var "l") (.var "x")) (.var "l"))
def reboxDecl : FunDecl := ⟨1, ⟨[("x", .boxT)], fun _ => reboxBody, .boxT, true⟩⟩
def reboxImpl (τ : Ty) : FunImpl := reboxDecl.concretise ⟨τ, PUnit.unit⟩

/-- `cycle<T>(x : Box<T>) -> Box<T>`: `let _ = store x x in x`.  It overwrites the value the
box holds with the head pointer itself, so the head cell points at itself. -/
abbrev cycleBody : Expr :=
  .letIn .anon (.store (.var "x") (.var "x")) (.var "x")
def cycleDecl : FunDecl := ⟨1, ⟨[("x", .boxT)], fun _ => cycleBody, .boxT, true⟩⟩
def cycleImpl (τ : Ty) : FunImpl := cycleDecl.concretise ⟨τ, PUnit.unit⟩

/-- `p == ()`: the test the drop glue performs on the value it reads out of a box. -/
abbrev isUnitTest (p : Pure) : Pure := p.eq .unit

/-- `drop<T>(x : Box<T>) -> Unit`: the drop glue reads the value the box holds and checks
whether it is the unit value.  The language has no loops, so the loop is encoded by making
the function *recursive*: when the value read is not unit it is a pointer, so the cell is
freed and the glue is applied to that pointer in turn; when it is unit there is nothing
left to free.  The two cases of the test are the two branches of a `choice`, guarded by an
`assume` of the guard, respectively of its negation.  The recursive call is made at the type
argument `T` the body is concretised at. -/
abbrev dropBody (T : Ty) : Expr :=
  .letIn (.named "v") (.load (.var "x"))
    (.choice
      (.letIn (.named "g") (.pure (isUnitTest (.var "v")))
        (.letIn .anon (.assume (.var "g")) .unit))
      (.letIn (.named "g") (.pure (.not (isUnitTest (.var "v"))))
        (.letIn .anon (.assume (.var "g"))
          (.letIn .anon (.free (.var "x")) (.call "drop" [T] [.var "v"])))))
def dropDecl : FunDecl := ⟨1, ⟨[("x", .boxT)], fun T => dropBody T, .unit, true⟩⟩
def dropImpl (τ : Ty) : FunImpl := dropDecl.concretise ⟨τ, PUnit.unit⟩

/-- The `Box` library. -/
def boxLib : Library where
  implementations := fun f =>
    if f = "box" then boxDecl
    else if f = "rebox" then reboxDecl
    else if f = "cycle" then cycleDecl
    else if f = "drop" then dropDecl
    else Part.none
  paramsValid := by
    intro f φ hφ; split_ifs at hφ <;> simp at hφ <;> subst hφ <;>
      exact ⟨by simp [FunDecl.ParamsNodup, FunDecl.paramNames, FunTempl.paramNames,
          boxDecl, reboxDecl, cycleDecl, dropDecl],
        by decide⟩
  tyParamsOrdered := by
    intro f φ hφ; split_ifs at hφ <;> simp at hφ <;> subst hφ <;> decide

theorem boxLib_box : boxLib.MapsTo "box" boxDecl := by
  simp [Library.MapsTo, boxLib]
theorem boxLib_rebox : boxLib.MapsTo "rebox" reboxDecl := by
  simp [Library.MapsTo, boxLib]
theorem boxLib_cycle : boxLib.MapsTo "cycle" cycleDecl := by
  simp [Library.MapsTo, boxLib]
theorem boxLib_drop : boxLib.MapsTo "drop" dropDecl := by
  simp [Library.MapsTo, boxLib]

theorem boxLib_inst_box (τ : Ty) : boxLib.Instantiates "box" [τ] (boxImpl τ) :=
  boxLib.instantiates_concretise boxLib_box ⟨τ, PUnit.unit⟩
theorem boxLib_inst_rebox (τ : Ty) : boxLib.Instantiates "rebox" [τ] (reboxImpl τ) :=
  boxLib.instantiates_concretise boxLib_rebox ⟨τ, PUnit.unit⟩
theorem boxLib_inst_cycle (τ : Ty) : boxLib.Instantiates "cycle" [τ] (cycleImpl τ) :=
  boxLib.instantiates_concretise boxLib_cycle ⟨τ, PUnit.unit⟩
theorem boxLib_inst_drop (τ : Ty) : boxLib.Instantiates "drop" [τ] (dropImpl τ) :=
  boxLib.instantiates_concretise boxLib_drop ⟨τ, PUnit.unit⟩

/-! ### Heaps with fresh blocks -/

/-- A one-cell block holding `v`, as a heap. -/
def blockOf (b : Block) (v : Val) : Heap :=
  PFun.singleton b (.block 1 (PFun.singleton 0 (.val v)))
/-- A freed block, as a heap. -/
def freedOf (b : Block) : Heap := PFun.singleton b .freed

theorem hProp_blockOf (b : Block) (v : Val) : HProp (blockOf b v) (((b, 0) : Loc) ↦ v) :=
  ⟨rfl, rfl⟩
theorem hProp_freedOf (b : Block) : HProp (freedOf b) (((b, 0) : Loc) ↦∅) := ⟨rfl, rfl⟩

/-- Any finite set of blocks misses some block. -/
theorem exists_notMem_of_finite {s : Set Block} (hfin : s.Finite) : ∃ b : Block, b ∉ s := by
  by_contra hc
  push_neg at hc
  exact Set.infinite_univ (hfin.subset fun x _ => hc x)

/-- A block outside the domain of a finite heap. -/
theorem exists_fresh_block {h : Heap} (hfin : h.dom.Finite) :
    ∃ b : Block, h b = Part.none := by
  obtain ⟨b, hb⟩ := exists_notMem_of_finite hfin
  exact ⟨b, Part.eq_none_iff'.mpr fun hd => hb hd⟩

/-- Two distinct blocks outside the domain of a finite heap. -/
theorem exists_two_fresh_blocks {h : Heap} (hfin : h.dom.Finite) :
    ∃ b₁ b₂ : Block, b₁ ≠ b₂ ∧ h b₁ = Part.none ∧ h b₂ = Part.none := by
  obtain ⟨b₁, hb₁⟩ := exists_notMem_of_finite hfin
  obtain ⟨b₂, hb₂⟩ := exists_notMem_of_finite (hfin.union (Set.finite_singleton b₁))
  exact ⟨b₁, b₂, fun hb => hb₂ (Or.inr hb.symm), Part.eq_none_iff'.mpr fun hd => hb₁ hd,
    Part.eq_none_iff'.mpr fun hd => hb₂ (Or.inl hd)⟩

/-! ### Basic manipulations of separating conjunctions -/

theorem hPure_star_intro {P : Prop} {Q : Asrt} {h : Heap} (hP : P) (hQ : HProp h Q) :
    HProp h (⌞P⌟ ∗ Q) :=
  ⟨∅, h, (PFun.empty_union h).symm, PFun.disjoint_empty_left h, ⟨rfl, hP⟩, hQ⟩

theorem hPure_star_elim {P : Prop} {Q : Asrt} {h : Heap} (hh : HProp h (⌞P⌟ ∗ Q)) :
    P ∧ HProp h Q := by
  obtain ⟨h₁, h₂, rfl, -, ⟨rfl, hP⟩, hQ⟩ := hh
  rw [PFun.empty_union]
  exact ⟨hP, hQ⟩

theorem hProp_star_emp_intro {P : Asrt} {h : Heap} (hP : HProp h P) : HProp h (P ∗ .emp) :=
  ⟨h, ∅, (PFun.union_empty h).symm, PFun.disjoint_empty_right h, hP, rfl⟩

theorem hProp_star_emp_elim {P : Asrt} {h : Heap} (hh : HProp h (P ∗ .emp)) : HProp h P := by
  obtain ⟨h₁, h₂, rfl, -, hP, (rfl : h₂ = ∅)⟩ := hh
  rwa [PFun.union_empty]

theorem hProp_star_congr_left {P P' Q : Asrt} (hP : ∀ h, HProp h P ↔ HProp h P') {h : Heap} :
    HProp h (P ∗ Q) ↔ HProp h (P' ∗ Q) :=
  hProp_star_comm.trans ((hProp_star_congr_right hP).trans hProp_star_comm)

theorem Heap.union_left_comm {a b c : Heap} (d : a ##ₘ b) : a ∪ (b ∪ c) = b ∪ (a ∪ c) := by
  rw [← PFun.union_assoc, PFun.union_comm d, PFun.union_assoc]

/-- Introduction rule for a right-nested three-way separating conjunction. -/
theorem hProp_star_star_intro {A B C : Asrt} {ha hb hc : Heap}
    (hA : HProp ha A) (hB : HProp hb B) (hC : HProp hc C)
    (dab : ha ##ₘ hb) (dac : ha ##ₘ hc) (dbc : hb ##ₘ hc) :
    HProp (ha ∪ (hb ∪ hc)) (A ∗ (B ∗ C)) :=
  ⟨ha, hb ∪ hc, rfl, PFun.disjoint_union_right.mpr ⟨dab, dac⟩, hA, hb, hc, rfl, dbc, hB, hC⟩

/-- Elimination rule for a right-nested three-way separating conjunction. -/
theorem hProp_star_star_elim {A B C : Asrt} {h : Heap} (hh : HProp h (A ∗ (B ∗ C))) :
    ∃ ha hb hc, h = ha ∪ (hb ∪ hc) ∧ ha ##ₘ hb ∧ ha ##ₘ hc ∧ hb ##ₘ hc ∧
      HProp ha A ∧ HProp hb B ∧ HProp hc C := by
  obtain ⟨ha, hbc, rfl, d, hA, hb, hc, rfl, dbc, hB, hC⟩ := hh
  obtain ⟨dab, dac⟩ := PFun.disjoint_union_right.mp d
  exact ⟨ha, hb, hc, rfl, dab, dac, dbc, hA, hB, hC⟩

/-! ### The common allocation pattern

Both `box` and `rebox` allocate a fresh one-cell block and store the input value into it; the
resources owned by the input value are abstracted into the frame `A`. -/

/-- The telescope of the RISL derivations below: one allocated location, the input value,
the result value of the picked summary and the typed subvariant supplied for the type
parameter of the call, the small binders being lifted. -/
abbrev bTele : Tele.{1} :=
  [tele (_ : Lifted.{1} Loc) (_ : Lifted.{1} Val) (_ : Lifted.{1} Val) (_ : TypedSubvariants.{0})]
/-- The telescope of the derivations that mention two allocated locations. -/
abbrev bTele₂ : Tele.{1} :=
  [tele (_ : Lifted.{1} Loc) (_ : Lifted.{1} Loc) (_ : Lifted.{1} Val) (_ : Lifted.{1} Val)
    (_ : TypedSubvariants.{0})]

/-- Generic RISL derivation for `let l = alloc 1 in let _ = store l rv in l`: it allocates
the fresh location `l₂`, fills it with `rv` and returns it, framing the resources `A`. -/
theorem wfSpec_alloc_store (A : Loc → Loc → Val → Val → TypedSubvariants.{0} → Asrt.{0}) :
    (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val)
        (rv : Lifted.{1} Val) (ts : TypedSubvariants.{0}),
      ⌈ A l₂.down l₁.down v.down rv.down ts ∗ .emp ⌉
      (Expr.letIn (.named "l") (.alloc (.int 1))
        (.letIn .anon (.store (.var "l") (.val rv.down)) (.var "l")))
      ⌈ .lok : λₗ r, A l₂.down l₁.down v.down rv.down ts ∗
          (⌞ r = .loc l₂.down ⌟ ∗ l₂.down ↦ rv.down) ⌉ := by
  -- allocate a fresh block, specialised to the location `l₂` of the telescope
  have Dalloc : (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (_l₁ : Lifted.{1} Loc)
      (_v : Lifted.{1} Val) (_rv : Lifted.{1} Val) (_ts : TypedSubvariants.{0}),
      ⌈ Asrt.emp ⌉ (Expr.alloc (.int 1))
      ⌈ .lok : λₗ r, ⌞ r = .loc l₂.down ⌟ ∗ l₂.down ↦? ⌉ :=
    .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) (fun _ _ hh => hh)
      (by rintro r ⟨l₂, l₁, v, rv, ts⟩ h hh; exact ⟨.up l₂.down, hh⟩) (fun _ => rfl)
      (.reindex (tt := [tele]) (fun _ => PUnit.unit) .alloc)
  -- frame the resources of the input value
  have Dalloc' : (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc)
      (v : Lifted.{1} Val) (rv : Lifted.{1} Val) (ts : TypedSubvariants.{0}),
      ⌈ A l₂.down l₁.down v.down rv.down ts ∗ .emp ⌉ (Expr.alloc (.int 1))
      ⌈ .lok : λₗ r, A l₂.down l₁.down v.down rv.down ts ∗
          (⌞ r = .loc l₂.down ⌟ ∗ l₂.down ↦?) ⌉ :=
    .frame (tt := bTele₂) (R := fun l₂ l₁ v rv ts => A l₂.down l₁.down v.down rv.down ts) Dalloc
  -- store the input value into the freshly allocated block
  have Dstore : (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc)
      (v : Lifted.{1} Val) (rv : Lifted.{1} Val) (ts : TypedSubvariants.{0}),
      ⌈ (A l₂.down l₁.down v.down rv.down ts ∗ ⌞ Val.loc l₂.down = .loc l₂.down ⌟) ∗ l₂.down ↦? ⌉
      (Expr.store (.val (.loc l₂.down)) (.val rv.down))
      ⌈ .lok : λₗ r, (A l₂.down l₁.down v.down rv.down ts ∗
            ⌞ Val.loc l₂.down = .loc l₂.down ⌟) ∗
          (⌞ r = .unit ⌟ ∗ l₂.down ↦ rv.down) ⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?pre ?post (fun _ => rfl)
      (.frame (tt := bTele₂)
        (R := fun l₂ l₁ v rv ts => A l₂.down l₁.down v.down rv.down ts)
        (.reindex (tt := [tele (_ : Lifted.{1} Val) (_ : Lifted.{1} Loc) (_ : Lifted.{1} Val)])
          (tt' := bTele₂)
          (fun ⟨l₂, _, _, rv, _, _⟩ => ⟨.up (Val.loc l₂.down), l₂, rv, PUnit.unit⟩) .store_uninit))
    case pre => exact fun _ _ hh => hProp_star_assoc.mpr hh
    case post => exact fun _ _ _ hh => hProp_star_assoc.mp hh
  -- return the location of the box
  have Dret : (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc)
      (v : Lifted.{1} Val) (rv : Lifted.{1} Val) (ts : TypedSubvariants.{0}),
      ⌈ (A l₂.down l₁.down v.down rv.down ts ∗ ⌞ Val.loc l₂.down = .loc l₂.down ⌟) ∗
          (⌞ Val.unit = .unit ⌟ ∗ l₂.down ↦ rv.down) ⌉
      (Expr.pure (.val (.loc l₂.down)))
      ⌈ .lok : λₗ r, A l₂.down l₁.down v.down rv.down ts ∗
          (⌞ r = .loc l₂.down ⌟ ∗ l₂.down ↦ rv.down) ⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?pre ?post
      (fun _ => rfl)
      (.frame (tt := bTele₂)
        (R := fun l₂ l₁ v rv ts =>
          (A l₂.down l₁.down v.down rv.down ts ∗ ⌞ Val.loc l₂.down = .loc l₂.down ⌟) ∗
            (⌞ Val.unit = .unit ⌟ ∗ l₂.down ↦ rv.down))
        (.reindex (tt := [tele (_ : Lifted.{1} Pure)]) (tt' := bTele₂)
          (fun ⟨l₂, _, _, _, _, _⟩ => ⟨.up (Pure.val (.loc l₂.down)), PUnit.unit⟩) .pure))
    case pre => exact fun _ _ hh => hProp_star_emp_elim hh
    case post =>
      rintro r ⟨l₂, l₁, v, rv, ts⟩ h hh
      obtain ⟨ha, hb, rfl, hdisj, hA, hrest⟩ := hh
      obtain ⟨hr, hpt⟩ := hPure_star_elim hrest
      subst hr
      exact ⟨ha ∪ hb, ∅, (PFun.union_empty _).symm, PFun.disjoint_empty_right _,
        ⟨ha, hb, rfl, hdisj,
          ⟨ha, ∅, (PFun.union_empty ha).symm, PFun.disjoint_empty_right ha, hA, ⟨rfl, rfl⟩⟩,
          hPure_star_intro rfl hpt⟩, ⟨rfl, rfl⟩⟩
  -- sequence the store and the return
  have Dinner : (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc)
      (v : Lifted.{1} Val) (rv : Lifted.{1} Val) (ts : TypedSubvariants.{0}),
      ⌈ A l₂.down l₁.down v.down rv.down ts ∗
          (⌞ Val.loc l₂.down = .loc l₂.down ⌟ ∗ l₂.down ↦?) ⌉
      (Expr.letIn .anon (.store (.val (.loc l₂.down)) (.val rv.down))
        (.pure (.val (.loc l₂.down))))
      ⌈ .lok : λₗ r, A l₂.down l₁.down v.down rv.down ts ∗
          (⌞ r = .loc l₂.down ⌟ ∗ l₂.down ↦ rv.down) ⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?pre
      (fun _ _ _ hh => hh) (fun _ => rfl)
      (.letIn (tt := bTele₂) (x := .anon) (v := fun _ _ _ _ _ => .up Val.unit)
        (e₁ := fun l₂ _ _ rv _ => .up (Expr.store (.val (.loc l₂.down)) (.val rv.down)))
        (e₂ := fun l₂ _ _ _ _ => .up (Expr.pure (.val (.loc l₂.down)))) Dstore Dret)
    case pre => exact fun _ _ hh => hProp_star_assoc.mp hh
  -- sequence the allocation and the rest of the body
  exact .letIn (tt := bTele₂) (x := .named "l") (v := fun l₂ _ _ _ _ => .up (Val.loc l₂.down))
    (e₁ := fun _ _ _ _ _ => .up (Expr.alloc (.int 1)))
    (e₂ := fun _ _ _ rv _ =>
      .up (Expr.letIn .anon (.store (.var "l") (.val rv.down)) (.var "l")))
    Dalloc' Dinner


end RUXt
