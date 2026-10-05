import RUXt.Examples.Box.Library

namespace RUXt

open scoped PFun

/-!
# Refuting the `Box` library

The four iterations of the refutation algorithm on the `Box` library of
`RUXt/Examples/Box/Library.lean`, in the order `box -> rebox -> cycle -> drop`, and the
inadequacy of the library they witness (`box_inadequate`).

After `box` and `rebox` the structure is `l₂ ↦ l₁, l₁ ↦ v`, and `cycle` turns the head cell
into a self-loop `l₂ ↦ l₂`.  The drop glue then reads `l₂` out of `l₂`, frees `l₂` and is
called on `l₂` again, whose first `load` reads a freed cell: a use-after-free.
-/

/-! ### Iteration 1: `box` -/

/-- Picks for `box`: the identity summary for the type parameter. -/
def ςsBox : Picks := [(.param 0, Summary.id boxLib)]

/-- Simplified postcondition of `box`: a box `l` holding the input value, which owns its
resources through the typed subvariant supplied for the type parameter. -/
def boxSubv : boxDecl.Subvariant ςsBox :=
  fun r v ts => .ex fun l =>
    ⌞ r = .loc l ⌟ ∗ (l ↦ v.down ∗ ts.get boxLib 0 v.down)

/-- `boxSubv` only reads the typed subvariant supplied for its type parameter at rank `0`. -/
theorem boxSubv_at_congr (r : Val) (args : TeleArg (ςsBox.teleOf.app (.uniform Val ςsBox.valArity)))
    (S T : SubvArgs.{0} (boxDecl.tyArity + ςsBox.freeArity))
    (hST : ∀ w, (S.get 0).get boxLib 0 w = (T.get 0).get boxLib 0 w) :
    (boxSubv r).at args S = (boxSubv r).at args T := by
  obtain ⟨s, ⟨⟩⟩ := S
  obtain ⟨t, ⟨⟩⟩ := T
  obtain ⟨v, ⟨⟩⟩ := args
  have hst : s.get boxLib 0 v = t.get boxLib 0 v := hST v
  show (Asrt.ex fun l => ⌞ r = .loc l ⌟ ∗ (l ↦ v ∗ s.get boxLib 0 v))
    = Asrt.ex fun l => ⌞ r = .loc l ⌟ ∗ (l ↦ v ∗ t.get boxLib 0 v)
  rw [hst]

/-- The postcondition obtained from executing the `box` function. -/
def boxPost : ςsBox.DerivedPost 1 :=
  fun r v rv ts =>
    ⌞ rv.down = v.down ⌟ ∗
      (.ex fun l => ⌞ r = .loc l ⌟ ∗ (l ↦ rv.down ∗ ts.get boxLib 0 v.down))

theorem boxPost_simplifiesTo : boxPost.SimplifiesTo semSolver boxSubv :=
  semSolver_simplifiesTo.mpr <| by
    rintro r ⟨v, ⟨⟩⟩ ⟨ts, ⟨⟩⟩ h
    constructor
    · rintro ⟨l, hh⟩
      exact ⟨⟨v, PUnit.unit⟩, hPure_star_intro rfl ⟨l, hh⟩⟩
    · rintro ⟨⟨rv, ⟨⟩⟩, hh⟩
      have h₁ : rv = v := (hPure_star_elim hh).1
      subst h₁
      exact (hPure_star_elim hh).2

def boxSumm : Summary := boxDecl.summary "box" ςsBox boxSubv
def boxCtx : SummCtx := SummCtx.update (SummCtx.base boxLib) .boxT boxSumm

theorem tryRefute_box : boxLib.TryRefute risl semSolver (SummCtx.base boxLib) (.inl (.boxT, boxSumm)) := by
  refine ⟨"box", boxDecl, boxLib_box, rfl, ςsBox, ⟨by decide, ?summIncl⟩,
    .lok, boxPost, ?derivPost, boxSubv, boxPost_simplifiesTo,
    ?satPost, rfl, rfl⟩
  case summIncl =>
    rintro ⟨τ, ς⟩ h
    simp only [ςsBox, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [SummCtx.base, SummCtx.update, SummCtx.MemTy]
  case satPost =>
    refine (semSolver_sat_owned_symAsrt (ς := boxDecl.summary "box" ςsBox boxSubv)).mpr ?_
    -- The postcondition is satisfiable at the placeholder typed subvariant and the unit
    -- input value, which owns an inhabitant of it in the empty state.
    have hown : HProp (∅ : Heap) ((default : TypedSubvariants.{0}).get boxLib 0 Val.unit) :=
      hProp_empty_get_default boxLib 0
    obtain ⟨b, hb⟩ := exists_fresh_block
      (hProp_opaque_finite (hProp_empty_opaque_unit.{0} boxLib))
    have hdisj : blockOf b Val.unit ##ₘ (∅ : Heap) :=
      PFun.disjoint_insert_left.mpr ⟨hb, PFun.disjoint_empty_left ∅⟩
    refine ⟨⟨Val.unit, PUnit.unit⟩, ⟨Ty.unit, PUnit.unit⟩, .loc (b, 0),
      blockOf b Val.unit ∪ ∅, ?_⟩
    rw [FunDecl.hProp_summary_ownedAt boxDecl "box" ςsBox boxSubv]
    exact ⟨(b, 0), ∅, blockOf b Val.unit ∪ ∅,
      (PFun.empty_union _).symm, PFun.disjoint_empty_left _, ⟨rfl, rfl⟩,
      blockOf b Val.unit, ∅, rfl, hdisj, hProp_blockOf b Val.unit, hown⟩
  case derivPost =>
    refine ⟨SpecCtx.fromPicks ςsBox "box" boxLib boxDecl.tyArity .lok boxPost,
      ⟨.update (φ := boxDecl) (tys := ςsBox.callTyArgs 1) (vals := ςsBox.callValArgs boxLib 1)
          .empty rfl boxLib_box ?bodyTriple, ?callRule⟩⟩
    case callRule =>
      exact wfSpec_mergeCall ςsBox "box" boxLib boxDecl.tyArity .lok boxPost
        (by simp [SpecCtx.update_apply])
    case bodyTriple =>
      refine .cons (tt := ςsBox.callTele 1) (tt' := ςsBox.callTele 1) id
        (fun _ => List.Subset.refl _) ?pre ?post (fun _ => rfl)
        (.ex (tt := ςsBox.callTele 1) (X := Loc)
          (e := fun _ rv _ => ULift.up (Expr.letIn (.named "l") (.alloc (.int 1))
            (.letIn .anon (.store (.var "l") (.val rv.down)) (.var "l"))))
          (.ex (tt := bTele) (X := Loc)
            (e := fun _ _ rv _ => ULift.up (Expr.letIn (.named "l") (.alloc (.int 1))
              (.letIn .anon (.store (.var "l") (.val rv.down)) (.var "l"))))
            (wfSpec_alloc_store fun _ _ v rv ts => ⌞ rv = v ⌟ ∗ ts.get boxLib 0 v)))
      case pre =>
        rintro ⟨v, rv, ts, ⟨⟩⟩ h ⟨l₁, l₂, hh⟩
        simp only [polyAsrt_apply, Picks.mergeOwned, ςsBox, Picks.merge_cons, hProp_star,
          Summary.id_ownedAt]
        exact hh
      case post =>
        rintro r ⟨v, rv, ts, ⟨⟩⟩ h hh
        obtain ⟨hrv, hh⟩ := hPure_star_elim hh
        obtain ⟨l, hh⟩ := hh
        obtain ⟨hr, hh⟩ := hPure_star_elim hh
        obtain ⟨h₃, h₄, rfl, hdisj, hpt, hop⟩ := hh
        subst hr
        exact ⟨l, l, h₄, h₃, PFun.union_comm hdisj, hdisj.symm,
          hPure_star_intro hrv hop, hPure_star_intro rfl hpt⟩

/-! ### Iteration 2: `rebox` -/

/-- Picks for `rebox`: the box summary obtained in iteration 1. -/
def ςsRebox : Picks := [(.boxT, boxSumm)]

/-- Simplified postcondition of `rebox`: a box `l₂` pointing at the box `l₁` of the input. -/
def reboxSubv : reboxDecl.Subvariant ςsRebox :=
  fun r v ts => .ex fun l₁ => .ex fun l₂ =>
    ⌞ r = .loc l₂ ⌟ ∗ (l₂ ↦ .loc l₁ ∗ (l₁ ↦ v.down ∗ ts.get boxLib 0 v.down))

/-- `reboxSubv` only reads the typed subvariant supplied for its type parameter at rank `0`. -/
theorem reboxSubv_at_congr (r : Val)
    (args : TeleArg (ςsRebox.teleOf.app (.uniform Val ςsRebox.valArity)))
    (S T : SubvArgs.{0} (reboxDecl.tyArity + ςsRebox.freeArity))
    (hST : ∀ w, (S.get 0).get boxLib 0 w = (T.get 0).get boxLib 0 w) :
    (reboxSubv r).at args S = (reboxSubv r).at args T := by
  obtain ⟨s, ⟨⟩⟩ := S
  obtain ⟨t, ⟨⟩⟩ := T
  obtain ⟨v, ⟨⟩⟩ := args
  have hst : s.get boxLib 0 v = t.get boxLib 0 v := hST v
  show (Asrt.ex fun l₁ => Asrt.ex fun l₂ => ⌞ r = .loc l₂ ⌟ ∗ (l₂ ↦ .loc l₁ ∗ (l₁ ↦ v ∗ s.get boxLib 0 v)))
    = Asrt.ex fun l₁ => Asrt.ex fun l₂ => ⌞ r = .loc l₂ ⌟ ∗ (l₂ ↦ .loc l₁ ∗ (l₁ ↦ v ∗ t.get boxLib 0 v))
  rw [hst]

/-- The postcondition obtained from executing the `rebox` function. -/
def reboxPost : ςsRebox.DerivedPost 1 :=
  fun r v rv ts => .ex fun l₁ => .ex fun l₂ =>
    (⌞ rv.down = .loc l₁ ⌟ ∗ (l₁ ↦ v.down ∗ ts.get boxLib 0 v.down)) ∗
      (⌞ r = .loc l₂ ⌟ ∗ l₂ ↦ rv.down)

theorem reboxPost_simplifiesTo : reboxPost.SimplifiesTo semSolver reboxSubv :=
  semSolver_simplifiesTo.mpr <| by
    rintro r ⟨v, ⟨⟩⟩ ⟨ts, ⟨⟩⟩ h
    constructor
    · rintro ⟨l₁, l₂, hh⟩
      obtain ⟨hr, hh⟩ := hPure_star_elim hh
      obtain ⟨ha, hb, rfl, hdisj, hpt, hrest⟩ := hh
      exact ⟨⟨.loc l₁, PUnit.unit⟩, l₁, l₂, hb, ha, PFun.union_comm hdisj, hdisj.symm,
        hPure_star_intro rfl hrest, hPure_star_intro hr hpt⟩
    · rintro ⟨⟨rv, ⟨⟩⟩, l₁, l₂, ha, hb, rfl, hdisj, hA, hB⟩
      obtain ⟨hrv, hrest⟩ := hPure_star_elim hA
      obtain ⟨hr, hpt⟩ := hPure_star_elim hB
      subst hrv
      exact ⟨l₁, l₂, hPure_star_intro hr
        ⟨hb, ha, PFun.union_comm hdisj, hdisj.symm, hpt, hrest⟩⟩

def reboxSumm : Summary := reboxDecl.summary "rebox" ςsRebox reboxSubv
def reboxCtx : SummCtx := SummCtx.update boxCtx .boxT reboxSumm

theorem tryRefute_rebox : boxLib.TryRefute risl semSolver boxCtx (.inl (.boxT, reboxSumm)) := by
  refine ⟨"rebox", reboxDecl, boxLib_rebox, rfl, ςsRebox, ⟨by decide, ?summIncl⟩,
    .lok, reboxPost, ?derivPost, reboxSubv, reboxPost_simplifiesTo,
    ?satPost, rfl, rfl⟩
  case summIncl =>
    rintro ⟨τ, ς⟩ h
    simp only [ςsRebox, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [boxCtx, SummCtx.update, SummCtx.MemTy]
  case satPost =>
    refine (semSolver_sat_owned_symAsrt (ς := reboxDecl.summary "rebox" ςsRebox reboxSubv)).mpr ?_
    -- The postcondition is satisfiable at the placeholder typed subvariant and the unit
    -- input value, which owns an inhabitant of it in the empty state.
    have hown : HProp (∅ : Heap) ((default : TypedSubvariants.{0}).get boxLib 0 Val.unit) :=
      hProp_empty_get_default boxLib 0
    obtain ⟨b₁, b₂, hne, hb₁, hb₂⟩ := exists_two_fresh_blocks
      (hProp_opaque_finite (hProp_empty_opaque_unit.{0} boxLib))
    have hd₁ : blockOf b₁ Val.unit ##ₘ (∅ : Heap) :=
      PFun.disjoint_insert_left.mpr ⟨hb₁, PFun.disjoint_empty_left ∅⟩
    have hd₂ : blockOf b₂ (.loc (b₁, 0)) ##ₘ (blockOf b₁ Val.unit ∪ ∅) :=
      PFun.disjoint_union_right.mpr
        ⟨PFun.disjoint_insert_left.mpr
            ⟨by simp [blockOf, PFun.singleton, Ne.symm hne], PFun.disjoint_empty_left _⟩,
          PFun.disjoint_insert_left.mpr ⟨hb₂, PFun.disjoint_empty_left ∅⟩⟩
    refine ⟨⟨Val.unit, PUnit.unit⟩, ⟨Ty.unit, PUnit.unit⟩, .loc (b₂, 0),
      blockOf b₂ (.loc (b₁, 0)) ∪ (blockOf b₁ Val.unit ∪ ∅), ?_⟩
    rw [FunDecl.hProp_summary_ownedAt reboxDecl "rebox" ςsRebox reboxSubv]
    exact ⟨(b₁, 0), (b₂, 0), ∅, _, (PFun.empty_union _).symm, PFun.disjoint_empty_left _,
      ⟨rfl, rfl⟩, blockOf b₂ (.loc (b₁, 0)), blockOf b₁ Val.unit ∪ ∅, rfl, hd₂,
      hProp_blockOf b₂ (.loc (b₁, 0)), blockOf b₁ Val.unit, ∅, rfl, hd₁,
      hProp_blockOf b₁ Val.unit, hown⟩
  case derivPost =>
    refine ⟨SpecCtx.fromPicks ςsRebox "rebox" boxLib reboxDecl.tyArity .lok reboxPost,
      ⟨.update (φ := reboxDecl) (tys := ςsRebox.callTyArgs 1)
          (vals := ςsRebox.callValArgs boxLib 1)
          .empty rfl boxLib_rebox ?bodyTriple, ?callRule⟩⟩
    case callRule =>
      exact wfSpec_mergeCall ςsRebox "rebox" boxLib reboxDecl.tyArity .lok reboxPost
        (by simp [SpecCtx.update_apply])
    case bodyTriple =>
      refine .cons (tt := ςsRebox.callTele 1) (tt' := ςsRebox.callTele 1) id
        (fun _ => List.Subset.refl _) ?pre (fun _ _ _ hh => hh) (fun _ => rfl)
        (.ex (tt := ςsRebox.callTele 1) (X := Loc)
          (e := fun _ rv _ => ULift.up (Expr.letIn (.named "l") (.alloc (.int 1))
            (.letIn .anon (.store (.var "l") (.val rv.down)) (.var "l"))))
          (.ex (tt := bTele) (X := Loc)
            (e := fun _ _ rv _ => ULift.up (Expr.letIn (.named "l") (.alloc (.int 1))
              (.letIn .anon (.store (.var "l") (.val rv.down)) (.var "l"))))
            (wfSpec_alloc_store fun _ l₁ v rv ts =>
              ⌞ rv = .loc l₁ ⌟ ∗ (l₁ ↦ v ∗ ts.get boxLib 0 v))))
      case pre =>
        rintro ⟨v, rv, ts, ⟨⟩⟩ h ⟨l₁, _l₂, hh⟩
        simp only [polyAsrt_apply, Picks.mergeOwned, ςsRebox, Picks.merge_cons,
          boxSumm]
        refine (hProp_star_congr_left fun _ =>
          FunDecl.hProp_summary_ownedAt boxDecl "box" ςsBox boxSubv _ _ _).mpr ?_
        rw [boxSubv_at_congr (T := ⟨ts, PUnit.unit⟩)]
        · exact hProp_star_emp_intro ⟨l₁, hProp_star_emp_elim hh⟩
        · exact fun w => by rw [Picks.headSubvs_get_param _ _ _ _ (by decide) (by decide)]; rfl

/-! ### Iteration 3: `cycle` -/

/-- Picks for `cycle`: the rebox summary obtained in iteration 2. -/
def ςsCycle : Picks := [(.boxT, reboxSumm)]

/-- Simplified postcondition of `cycle`: the head cell of the box has been overwritten with
the head pointer itself, so that it points at itself. -/
def cycleSubv : cycleDecl.Subvariant ςsCycle :=
  fun r v ts => .ex fun l₁ => .ex fun l₂ =>
    ⌞ r = .loc l₂ ⌟ ∗ (l₂ ↦ .loc l₂ ∗ (l₁ ↦ v.down ∗ ts.get boxLib 0 v.down))

/-- `cycleSubv` only reads the typed subvariant supplied for its type parameter at rank `0`. -/
theorem cycleSubv_at_congr (r : Val)
    (args : TeleArg (ςsCycle.teleOf.app (.uniform Val ςsCycle.valArity)))
    (S T : SubvArgs.{0} (cycleDecl.tyArity + ςsCycle.freeArity))
    (hST : ∀ w, (S.get 0).get boxLib 0 w = (T.get 0).get boxLib 0 w) :
    (cycleSubv r).at args S = (cycleSubv r).at args T := by
  obtain ⟨s, ⟨⟩⟩ := S
  obtain ⟨t, ⟨⟩⟩ := T
  obtain ⟨v, ⟨⟩⟩ := args
  have hst : s.get boxLib 0 v = t.get boxLib 0 v := hST v
  show (Asrt.ex fun l₁ => Asrt.ex fun l₂ => ⌞ r = .loc l₂ ⌟ ∗ (l₂ ↦ .loc l₂ ∗ (l₁ ↦ v ∗ s.get boxLib 0 v)))
    = Asrt.ex fun l₁ => Asrt.ex fun l₂ => ⌞ r = .loc l₂ ⌟ ∗ (l₂ ↦ .loc l₂ ∗ (l₁ ↦ v ∗ t.get boxLib 0 v))
  rw [hst]

/-- The postcondition obtained from executing the `cycle` function. -/
def cyclePost : ςsCycle.DerivedPost 1 :=
  fun r v rv ts => .ex fun l₁ => .ex fun l₂ => ⌞ rv.down = .loc l₂ ⌟ ∗
    (⌞ r = .loc l₂ ⌟ ∗ (l₂ ↦ .loc l₂ ∗ (l₁ ↦ v.down ∗ ts.get boxLib 0 v.down)))

theorem cyclePost_simplifiesTo : cyclePost.SimplifiesTo semSolver cycleSubv :=
  semSolver_simplifiesTo.mpr <| by
    rintro r ⟨v, ⟨⟩⟩ ⟨ts, ⟨⟩⟩ h
    constructor
    · rintro ⟨l₁, l₂, hh⟩
      exact ⟨⟨.loc l₂, PUnit.unit⟩, l₁, l₂, hPure_star_intro rfl hh⟩
    · rintro ⟨⟨rv, ⟨⟩⟩, l₁, l₂, hh⟩
      exact ⟨l₁, l₂, (hPure_star_elim hh).2⟩

def cycleSumm : Summary := cycleDecl.summary "cycle" ςsCycle cycleSubv
def cycleCtx : SummCtx := SummCtx.update reboxCtx .boxT cycleSumm

/-- The RISL derivation for the body of `cycle`: it overwrites the contents of the head cell
`l₂` with the head pointer `l₂` itself and returns it, leaving the second cell `l₁` of the
chain untouched.  The resources the input value owns are abstracted into `A`. -/
theorem wfSpec_cycleBody (A : Val → TypedSubvariants.{0} → Asrt.{0}) :
    (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val)
        (rv : Lifted.{1} Val) (ts : TypedSubvariants.{0}),
      ⌈ (⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₁.down ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ∗ .emp ⌉
      (Expr.letIn .anon (.store (.val rv.down) (.val rv.down)) (.pure (.val rv.down)))
      ⌈ .lok : λₗ r, ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ r = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₂.down ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉ := by
  -- overwrite the contents of the head cell with the head pointer
  have Dstore : (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val)
        (rv : Lifted.{1} Val) (ts : TypedSubvariants.{0}),
      ⌈ (l₁.down ↦ v.down ∗ A v.down ts) ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ l₂.down ↦ .loc l₁.down) ⌉
      (Expr.store (.val rv.down) (.val rv.down))
      ⌈ .lok : λₗ r, (l₁.down ↦ v.down ∗ A v.down ts) ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l₂.down ↦ rv.down)) ⌉ :=
    .frame (tt := bTele₂)
      (R := fun _ l₁ v _ ts => l₁.down ↦ v.down ∗ A v.down ts)
      (.reindex (tt := [tele (_ : Lifted.{1} Val) (_ : Lifted.{1} Loc) (_ : Lifted.{1} Val)
          (_ : Lifted.{1} Val)]) (tt' := bTele₂)
        (fun ⟨l₂, l₁, _, rv, _, _⟩ => ⟨rv, l₂, rv, .up (.loc l₁.down), PUnit.unit⟩) .store)
  -- return the (now self-referential) box
  have Dret : (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val)
        (rv : Lifted.{1} Val) (ts : TypedSubvariants.{0}),
      ⌈ (l₁.down ↦ v.down ∗ A v.down ts) ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ (⌞ Val.unit = .unit ⌟ ∗ l₂.down ↦ rv.down)) ⌉
      (Expr.pure (.val rv.down))
      ⌈ .lok : λₗ r, ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ r = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₂.down ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?pre ?post (fun _ => rfl)
      (.frame (tt := bTele₂)
        (R := fun l₂ l₁ v rv ts => (l₁.down ↦ v.down ∗ A v.down ts) ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ (⌞ Val.unit = .unit ⌟ ∗ l₂.down ↦ rv.down)))
        (.reindex (tt := [tele (_ : Lifted.{1} Pure)]) (tt' := bTele₂)
          (fun ⟨_, _, _, rv, _, _⟩ => ⟨.up (Pure.val rv.down), PUnit.unit⟩) .pure))
    case pre => exact fun _ _ hh => hProp_star_emp_elim hh
    case post =>
      rintro r ⟨l₂, l₁, v, ⟨rv⟩, ts, ⟨⟩⟩ h hh
      obtain ⟨hrv, hh⟩ := hPure_star_elim hh
      obtain ⟨hr, hh⟩ := hPure_star_elim hh
      obtain ⟨h₂, h₁, hop, rfl, d21, d2o, d1o, hpt₂, hpt₁, hopP⟩ := hProp_star_star_elim hh
      subst hr
      have hrv' : rv = Val.loc l₂.down := hrv
      subst hrv'
      refine ⟨(h₁ ∪ hop) ∪ h₂, ∅, ?_, PFun.disjoint_empty_right _, ?_, ⟨rfl, rfl⟩⟩
      · rw [PFun.union_empty, PFun.union_comm (PFun.disjoint_union_left.mpr ⟨d21.symm, d2o.symm⟩)]
      · exact ⟨h₁ ∪ hop, h₂, rfl, PFun.disjoint_union_left.mpr ⟨d21.symm, d2o.symm⟩,
          ⟨h₁, hop, rfl, d1o, hpt₁, hopP⟩,
          hPure_star_intro rfl (hPure_star_intro rfl hpt₂)⟩
  -- sequence the store and the return
  refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?pre
    (fun _ _ _ hh => hh) (fun _ => rfl)
    (.letIn (tt := bTele₂) (x := .anon) (v := fun _ _ _ _ _ => ULift.up Val.unit)
      (e₁ := fun _ _ _ rv _ => ULift.up (Expr.store (.val rv.down) (.val rv.down)))
      (e₂ := fun _ _ _ rv _ => ULift.up (Expr.pure (.val rv.down)))
      Dstore Dret)
  case pre =>
    rintro ⟨l₂, l₁, v, rv, ts⟩ h hh
    obtain ⟨ha, h₂, rfl, d, hA, hrest⟩ := hh
    obtain ⟨hrv, hpt₂⟩ := hPure_star_elim hrest
    obtain ⟨h₁, hop, rfl, d1o, hpt₁, hopP⟩ := hA
    obtain ⟨d12, dop2⟩ := PFun.disjoint_union_left.mp d
    rw [PFun.union_comm d]
    exact hProp_star_emp_intro (hPure_star_intro hrv
      (hProp_star_star_intro hpt₂ hpt₁ hopP d12.symm dop2.symm d1o))

theorem tryRefute_cycle : boxLib.TryRefute risl semSolver reboxCtx (.inl (.boxT, cycleSumm)) := by
  refine ⟨"cycle", cycleDecl, boxLib_cycle, rfl, ςsCycle, ⟨by decide, ?summIncl⟩,
    .lok, cyclePost, ?derivPost, cycleSubv, cyclePost_simplifiesTo,
    ?satPost, rfl, rfl⟩
  case summIncl =>
    rintro ⟨τ, ς⟩ h
    simp only [ςsCycle, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [reboxCtx, SummCtx.update, SummCtx.MemTy]
  case satPost =>
    refine (semSolver_sat_owned_symAsrt (ς := cycleDecl.summary "cycle" ςsCycle cycleSubv)).mpr ?_
    -- The postcondition is satisfiable at the placeholder typed subvariant and the unit
    -- input value, which owns an inhabitant of it in the empty state.
    have hown : HProp (∅ : Heap) ((default : TypedSubvariants.{0}).get boxLib 0 Val.unit) :=
      hProp_empty_get_default boxLib 0
    obtain ⟨b₁, b₂, hne, hb₁, hb₂⟩ := exists_two_fresh_blocks
      (hProp_opaque_finite (hProp_empty_opaque_unit.{0} boxLib))
    have hd₁ : blockOf b₁ Val.unit ##ₘ (∅ : Heap) :=
      PFun.disjoint_insert_left.mpr ⟨hb₁, PFun.disjoint_empty_left ∅⟩
    have hd₂ : blockOf b₂ (.loc (b₂, 0)) ##ₘ (blockOf b₁ Val.unit ∪ ∅) :=
      PFun.disjoint_union_right.mpr
        ⟨PFun.disjoint_insert_left.mpr
            ⟨by simp [blockOf, PFun.singleton, Ne.symm hne], PFun.disjoint_empty_left _⟩,
          PFun.disjoint_insert_left.mpr ⟨hb₂, PFun.disjoint_empty_left ∅⟩⟩
    refine ⟨⟨Val.unit, PUnit.unit⟩, ⟨Ty.unit, PUnit.unit⟩, .loc (b₂, 0),
      blockOf b₂ (.loc (b₂, 0)) ∪ (blockOf b₁ Val.unit ∪ ∅), ?_⟩
    rw [FunDecl.hProp_summary_ownedAt cycleDecl "cycle" ςsCycle cycleSubv]
    exact ⟨(b₁, 0), (b₂, 0), ∅, _, (PFun.empty_union _).symm, PFun.disjoint_empty_left _,
      ⟨rfl, rfl⟩, blockOf b₂ (.loc (b₂, 0)), blockOf b₁ Val.unit ∪ ∅, rfl, hd₂,
      hProp_blockOf b₂ (.loc (b₂, 0)), blockOf b₁ Val.unit, ∅, rfl, hd₁,
      hProp_blockOf b₁ Val.unit, hown⟩
  case derivPost =>
    refine ⟨SpecCtx.fromPicks ςsCycle "cycle" boxLib cycleDecl.tyArity .lok cyclePost,
      ⟨.update (φ := cycleDecl) (tys := ςsCycle.callTyArgs 1)
          (vals := ςsCycle.callValArgs boxLib 1)
          .empty rfl boxLib_cycle ?bodyTriple, ?callRule⟩⟩
    case callRule =>
      exact wfSpec_mergeCall ςsCycle "cycle" boxLib cycleDecl.tyArity .lok cyclePost
        (by simp [SpecCtx.update_apply])
    case bodyTriple =>
      refine .cons (tt := ςsCycle.callTele 1) (tt' := ςsCycle.callTele 1) id
        (fun _ => List.Subset.refl _) ?pre (fun _ _ _ hh => hh) (fun _ => rfl)
        (.ex (tt := ςsCycle.callTele 1) (X := Loc)
          (e := fun _ rv _ => ULift.up (Expr.letIn .anon
            (.store (.val rv.down) (.val rv.down)) (.pure (.val rv.down))))
          (.ex (tt := bTele) (X := Loc)
            (e := fun _ _ rv _ => ULift.up (Expr.letIn .anon
              (.store (.val rv.down) (.val rv.down)) (.pure (.val rv.down))))
            (wfSpec_cycleBody fun v ts => ts.get boxLib 0 v)))
      case pre =>
        rintro ⟨v, rv, ts, ⟨⟩⟩ h ⟨l₁, l₂, hh⟩
        simp only [polyAsrt_apply, Picks.mergeOwned, ςsCycle, Picks.merge_cons,
          reboxSumm]
        refine (hProp_star_congr_left fun _ =>
          FunDecl.hProp_summary_ownedAt reboxDecl "rebox" ςsRebox reboxSubv
            _ _ _).mpr ?_
        rw [reboxSubv_at_congr (T := ⟨ts, PUnit.unit⟩)]
        · exact hProp_star_emp_intro ⟨l₁, l₂, hProp_star_emp_elim hh⟩
        · exact fun w => by rw [Picks.headSubvs_get_param _ _ _ _ (by decide) (by decide)]; rfl

/-! ### Iteration 4: `drop` -/

/-- Picks for `drop`: the cyclic summary obtained in iteration 3. -/
def ςsDrop : Picks := [(.boxT, cycleSumm)]

/-- Simplified postcondition of `drop`: the head cell of the cycle has been freed. -/
def dropSubv : dropDecl.Subvariant ςsDrop :=
  fun r v ts => .ex fun l₁ => .ex fun l₂ =>
    ⌞ r = .unit ⌟ ∗ (l₂ ↦∅ ∗ (l₁ ↦ v.down ∗ ts.get boxLib 0 v.down))

/-- The (erroneous) postcondition obtained from executing the `drop` function. -/
def dropPost : ςsDrop.DerivedPost 1 :=
  fun r v rv ts => .ex fun l₁ => .ex fun l₂ => ⌞ rv.down = .loc l₂ ⌟ ∗
    (⌞ r = .unit ⌟ ∗ (l₂ ↦∅ ∗ (l₁ ↦ v.down ∗ ts.get boxLib 0 v.down)))

theorem dropPost_simplifiesTo : dropPost.SimplifiesTo semSolver dropSubv :=
  semSolver_simplifiesTo.mpr <| by
    rintro r ⟨v, ⟨⟩⟩ ⟨ts, ⟨⟩⟩ h
    constructor
    · rintro ⟨l₁, l₂, hh⟩
      exact ⟨⟨.loc l₂, PUnit.unit⟩, l₁, l₂, hPure_star_intro rfl hh⟩
    · rintro ⟨⟨rv, ⟨⟩⟩, l₁, l₂, hh⟩
      exact ⟨l₁, l₂, (hPure_star_elim hh).2⟩

/-- The summary the last iteration derives.  It is never filed in the summary context — the
iteration ends in an error state — but its postcondition still has to be satisfiable. -/
def dropSumm : Summary := dropDecl.summary "drop" ςsDrop dropSubv

/-- On a pointer, the guard `¬ (v == ())` of the drop glue evaluates to `true`. -/
theorem eval_not_isUnitTest_loc (l : Loc) :
    some (Val.bool true) = (Pure.not (isUnitTest (.val (.loc l)))).eval := rfl

/-- The `assume`-guarded branch of the drop glue that performs the recursive free: when the
value `w` read out of the box is a pointer, the guard `¬ (w == ())` evaluates to `true`, the
`assume` succeeds, and the derivation continues with the body `k` of the branch. -/
theorem wfSpec_not_isUnitTest_branch {Γ : SpecCtx.{0}} {ε : LExit}
    (P : TeleArg bTele₂ → Asrt.{0}) (Φ : Val → TeleArg bTele₂ → Asrt.{0})
    (w : TeleArg bTele₂ → Val) (e₁ k : TeleArg bTele₂ → Expr)
    (hw : ∀ args h, HProp h (P args) →
      some (Val.bool true) = (Pure.not (isUnitTest (.val (w args)))).eval)
    (hk : ∀ args, (k args).substTerm "g" (.val (.bool true)) = k args)
    (hderiv : Γ ⊢ ⌈teleBind P⌉ (teleLift k) ⌈ε, fun r => teleBind (Φ r)⌉) :
    Γ ⊢ ⌈teleBind P⌉ (teleLift fun args => Expr.choice (e₁ args)
      (.letIn (.named "g") (.pure (.not (isUnitTest (.val (w args)))))
        (.letIn .anon (.assume (.var "g")) (k args))))
      ⌈ε, fun r => teleBind (Φ r)⌉ := by
  -- the body of the branch, once the guard has been assumed
  have Dbody : Γ ⊢ ⌈teleBind fun args => P args ∗ ⌞ Val.unit = .unit ⌟⌉
      (teleLift fun args => (k args).substTerm "g" (.val (.bool true)))
      ⌈ε, fun r => teleBind (Φ r)⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?_ ?_ ?_ hderiv
    · exact fun _ h hh => ⟨h, ∅, (PFun.union_empty h).symm, PFun.disjoint_empty_right h, hh,
        ⟨rfl, rfl⟩⟩
    · exact fun _ _ _ hh => hh
    · exact fun args => hk args
  -- the `assume` of the guard succeeds, since the guard has evaluated to `true`
  have Dass1 : Γ ⊢ ⌈teleBind P⌉ (teleLift fun _ => Expr.assume .true)
      ⌈ .lok, fun r => teleBind fun args => P args ∗ ⌞ r = .unit ⌟ ⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?_ ?_ ?_
      (.frame (tt := bTele₂) (R := teleBind P)
        (.reindex (tt := [tele]) (tt' := bTele₂) (fun _ => PUnit.unit) .assume))
    · exact fun _ _ hh => hProp_star_emp_elim hh
    · exact fun _ _ _ hh => hh
    · exact fun _ => rfl
  have Dassume : Γ ⊢ ⌈teleBind P⌉
      (teleLift fun args => Expr.letIn .anon (.assume .true)
        ((k args).substTerm "g" (.val (.bool true))))
      ⌈ε, fun r => teleBind (Φ r)⌉ :=
    .letIn (tt := bTele₂) (x := .anon) (v := teleLift fun _ => Val.unit)
      (e₁ := teleLift fun _ => Expr.assume .true)
      (e₂ := teleLift fun args => (k args).substTerm "g" (.val (.bool true)))
      Dass1 Dbody
  -- evaluate the guard, which is `true` because the value read out of the box is a pointer
  have Dguard : Γ ⊢ ⌈teleBind P⌉
      (teleLift fun args => Expr.pure (.not (isUnitTest (.val (w args)))))
      ⌈ .lok, fun r => teleBind fun args =>
        P args ∗ ⌞ some r = (Pure.not (isUnitTest (.val (w args)))).eval ⌟ ⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?_ ?_ ?_
      (.frame (tt := bTele₂) (R := teleBind P)
        (.reindex (tt := [tele (_ : Lifted.{1} Pure)]) (tt' := bTele₂)
          (fun args => ⟨.up (.not (isUnitTest (.val (w args)))), PUnit.unit⟩) .pure))
    · exact fun _ _ hh => hProp_star_emp_elim hh
    · exact fun _ _ _ hh => hh
    · exact fun _ => rfl
  have Dassume' : Γ ⊢ ⌈teleBind fun args =>
        P args ∗ ⌞ some (Val.bool true) = (Pure.not (isUnitTest (.val (w args)))).eval ⌟⌉
      (teleLift fun args => Expr.letIn .anon (.assume .true)
        ((k args).substTerm "g" (.val (.bool true))))
      ⌈ε, fun r => teleBind (Φ r)⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?_ ?_ ?_ Dassume
    · exact fun args h hh => ⟨h, ∅, (PFun.union_empty h).symm, PFun.disjoint_empty_right h, hh,
        ⟨rfl, hw args h hh⟩⟩
    · exact fun _ _ _ hh => hh
    · exact fun _ => rfl
  refine .choice (tt := bTele₂)
    (e₁ := teleLift e₁)
    (e₂ := teleLift fun args => Expr.letIn (.named "g")
      (.pure (.not (isUnitTest (.val (w args)))))
      (.letIn .anon (.assume (.var "g")) (k args)))
    (Or.inr rfl)
    (.letIn (tt := bTele₂) (x := .named "g") (v := teleLift fun _ => Val.bool true)
      (e₁ := teleLift fun args => Expr.pure (.not (isUnitTest (.val (w args)))))
      (e₂ := teleLift fun args => Expr.letIn .anon (.assume (.var "g")) (k args))
      Dguard Dassume')

/-- The specification of `drop` called on a location that has already been freed: its very
first `load` reads a freed cell.  The type argument is read off the typed subvariant `ts` bound
by the telescope (`τ ts`), and the argument is the symbolic value `rv`, recorded by the pre- and
postcondition to be the freed location `l₂`. -/
def dropSpecFreed (τ : TypedSubvariants.{0} → Ty) : FunSpec.{0} :=
  ⟨bTele₂, fun _ _ _ _ ts => ULift.up [τ ts], fun _ _ _ rv _ => ULift.up [rv.down],
    fun l₂ _ _ rv _ => ⌞ rv.down = .loc l₂.down ⌟ ∗ l₂.down ↦∅, .lerr,
    fun r l₂ _ _ rv _ => ⌞ rv.down = .loc l₂.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l₂.down ↦∅)⟩

/-- Context holding the (erroneous) recursive call of the drop glue. -/
def dropCtx₁ (τ : TypedSubvariants.{0} → Ty) : SpecCtx.{0} :=
  SpecCtx.update (dropSpecFreed τ) "drop" ∅

/-- The body of `drop` on an already freed location: the `load` faults immediately.  The
derivation is uniform in the type parameter `τ` the glue is instantiated at. -/
theorem wfSpec_dropBody_freed (τ : TypedSubvariants.{0} → Ty) :
    (∅ : SpecCtx.{0}) ⊢ λₗ (l₂ : Lifted.{1} Loc) (_l₁ : Lifted.{1} Loc) (_v : Lifted.{1} Val) (rv : Lifted.{1} Val)
        (ts : TypedSubvariants.{0}),
      ⌈ ⌞ rv.down = .loc l₂.down ⌟ ∗ l₂.down ↦∅ ⌉
      (Expr.letIn (.named "v") (.load (.val rv.down))
        (.choice
          (.letIn (.named "g") (.pure (isUnitTest (.var "v")))
            (.letIn .anon (.assume (.var "g")) .unit))
          (.letIn (.named "g") (.pure (.not (isUnitTest (.var "v"))))
            (.letIn .anon (.assume (.var "g"))
              (.letIn .anon (.free (.val rv.down)) (.call "drop" [τ ts] [.var "v"]))))))
      ⌈ .lerr : λₗ r, ⌞ rv.down = .loc l₂.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l₂.down ↦∅) ⌉ :=
  .let_cut (tt := bTele₂)
    (e₁ := fun _ _ _ rv _ => ULift.up (Expr.load (.val rv.down)))
    (e₂ := fun _ _ _ rv ts => ULift.up (Expr.choice
      (.letIn (.named "g") (.pure (isUnitTest (.var "v")))
        (.letIn .anon (.assume (.var "g")) .unit))
      (.letIn (.named "g") (.pure (.not (isUnitTest (.var "v"))))
        (.letIn .anon (.assume (.var "g"))
          (.letIn .anon (.free (.val rv.down)) (.call "drop" [τ ts] [.var "v"]))))))
    (.reindex (tt := [tele (_ : Lifted.{1} Val) (_ : Lifted.{1} Loc)]) (tt' := bTele₂)
      (fun ⟨l₂, _, _, rv, _, _⟩ => ⟨rv, l₂, PUnit.unit⟩) .load_freed) (by simp)

theorem wfSpecCtx_dropCtx₁ (τ : TypedSubvariants.{0} → Ty) : boxLib ≺ₛ dropCtx₁ τ :=
  .update (tt := bTele₂) (φ := dropDecl)
    (tys := fun _ _ _ _ ts => ULift.up ⟨τ ts, PUnit.unit⟩)
    (vals := fun _ _ _ rv _ => ULift.up ⟨rv.down, PUnit.unit⟩)
    .empty rfl boxLib_drop (wfSpec_dropBody_freed τ)

/-- The RISL derivation for the body of `drop` on the self-referential box: it reads the
head pointer `l₂` out of the head cell `l₂` itself, frees `l₂` and drops `l₂` once more,
whose `load` now reads the freed cell.  The derivation therefore ends in `.lerr`: a
use-after-free. -/
theorem wfSpec_dropBody (τ : TypedSubvariants.{0} → Ty)
    (A : Val → TypedSubvariants.{0} → Asrt.{0}) :
    dropCtx₁ τ ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val) (rv : Lifted.{1} Val)
        (ts : TypedSubvariants.{0}),
      ⌈ (⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₂.down ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ∗ .emp ⌉
      (Expr.letIn (.named "v") (.load (.val rv.down))
        (.choice
          (.letIn (.named "g") (.pure (isUnitTest (.var "v")))
            (.letIn .anon (.assume (.var "g")) .unit))
          (.letIn (.named "g") (.pure (.not (isUnitTest (.var "v"))))
            (.letIn .anon (.assume (.var "g"))
              (.letIn .anon (.free (.val rv.down)) (.call "drop" [τ ts] [.var "v"]))))))
      ⌈ .lerr : λₗ r, ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ r = .unit ⌟ ∗ (l₂.down ↦∅ ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉ := by
  -- read the head pointer out of the head cell
  have Dload : dropCtx₁ τ ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val) (rv : Lifted.{1} Val)
        (ts : TypedSubvariants.{0}),
      ⌈ ⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₂.down ∗ (l₁.down ↦ v.down ∗ A v.down ts)) ⌉
      (Expr.load (.val rv.down))
      ⌈ .lok : λₗ r, ⌞ r = .loc l₂.down ⌟ ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₂.down ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?_ ?_ (fun _ => rfl)
      (.frame (tt := bTele₂)
        (R := fun _ l₁ v _ ts => l₁.down ↦ v.down ∗ A v.down ts)
        (.reindex (tt := [tele (_ : Lifted.{1} Val) (_ : Lifted.{1} Loc) (_ : Lifted.{1} Val)])
          (tt' := bTele₂)
          (fun ⟨l₂, _, _, rv, _, _⟩ => ⟨rv, l₂, .up (.loc l₂.down), PUnit.unit⟩) .load))
    · rintro ⟨l₂, l₁, v, rv, ts⟩ h ⟨ha, h₂, rfl, d, hA, hrest⟩
      obtain ⟨hrv, hpt₂⟩ := hPure_star_elim hrest
      obtain ⟨h₁, hop, rfl, d1o, hpt₁, hopP⟩ := hA
      obtain ⟨d12, dop2⟩ := PFun.disjoint_union_left.mp d
      rw [PFun.union_comm d]
      exact hPure_star_intro hrv
        (hProp_star_star_intro hpt₂ hpt₁ hopP d12.symm dop2.symm d1o)
    · rintro r ⟨l₂, l₁, v, rv, ts⟩ h hh
      obtain ⟨hr, hh⟩ := hPure_star_elim hh
      obtain ⟨hrv, hh⟩ := hPure_star_elim hh
      obtain ⟨h₂, h₁, hop, rfl, d21, d2o, d1o, hpt₂, hpt₁, hopP⟩ := hProp_star_star_elim hh
      rw [PFun.union_comm (PFun.disjoint_union_right.mpr ⟨d21, d2o⟩)]
      exact ⟨h₁ ∪ hop, h₂, rfl, PFun.disjoint_union_left.mpr ⟨d21.symm, d2o.symm⟩,
        ⟨h₁, hop, rfl, d1o, hpt₁, hopP⟩, hPure_star_intro hrv (hPure_star_intro hr hpt₂)⟩
  -- free the head cell
  have Dfree : dropCtx₁ τ ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val) (rv : Lifted.{1} Val)
        (ts : TypedSubvariants.{0}),
      ⌈ ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₂.down ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉
      (Expr.free (.val rv.down))
      ⌈ .lok : λₗ r, ⌞ r = .unit ⌟ ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦∅ ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?_ ?_ (fun _ => rfl)
      (.frame (tt := bTele₂)
        (R := fun _ l₁ v _ ts => l₁.down ↦ v.down ∗ A v.down ts)
        (.reindex (tt := [tele (_ : Lifted.{1} Val) (_ : Lifted.{1} Loc) (_ : Lifted.{1} Val)])
          (tt' := bTele₂)
          (fun ⟨l₂, _, _, rv, _, _⟩ => ⟨rv, l₂, .up (.loc l₂.down), PUnit.unit⟩) .free))
    · rintro ⟨l₂, l₁, v, rv, ts⟩ h ⟨ha, h₂, rfl, d, hA, hrest⟩
      obtain ⟨hrv, hpt₂⟩ := hPure_star_elim hrest
      obtain ⟨h₁, hop, rfl, d1o, hpt₁, hopP⟩ := hA
      obtain ⟨d12, dop2⟩ := PFun.disjoint_union_left.mp d
      rw [PFun.union_comm d]
      exact hPure_star_intro hrv (hPure_star_intro hrv
        (hProp_star_star_intro hpt₂ hpt₁ hopP d12.symm dop2.symm d1o))
    · rintro r ⟨l₂, l₁, v, rv, ts⟩ h hh
      obtain ⟨hr, hh⟩ := hPure_star_elim hh
      obtain ⟨hrv, hh⟩ := hPure_star_elim hh
      obtain ⟨h₂, h₁, hop, rfl, d21, d2o, d1o, hpt₂, hpt₁, hopP⟩ := hProp_star_star_elim hh
      rw [PFun.union_comm (PFun.disjoint_union_right.mpr ⟨d21, d2o⟩)]
      exact ⟨h₁ ∪ hop, h₂, rfl, PFun.disjoint_union_left.mpr ⟨d21.symm, d2o.symm⟩,
        ⟨h₁, hop, rfl, d1o, hpt₁, hopP⟩, hPure_star_intro hrv (hPure_star_intro hr hpt₂)⟩
  -- call the drop glue, at the same type parameter, on the (already freed) head cell
  have Dcall : dropCtx₁ τ ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val) (rv : Lifted.{1} Val)
        (ts : TypedSubvariants.{0}),
      ⌈ ⌞ Val.unit = .unit ⌟ ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦∅ ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉
      (Expr.call "drop" [τ ts] [.val rv.down])
      ⌈ .lerr : λₗ r, ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ r = .unit ⌟ ∗ (l₂.down ↦∅ ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉ := by
    refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?_ ?_ (fun _ => rfl)
      (.frame (tt := bTele₂)
        (R := fun _ l₁ v _ ts => l₁.down ↦ v.down ∗ A v.down ts)
        (.call (f := "drop") (tt := bTele₂)
          (tys := fun _ _ _ _ ts => ULift.up [τ ts])
          (vals := fun _ _ _ rv _ => ULift.up [rv.down])
          (P := fun l₂ _ _ rv _ => ⌞ rv.down = .loc l₂.down ⌟ ∗ l₂.down ↦∅) (ε := .lerr)
          (Φ := fun r l₂ _ _ rv _ =>
            ⌞ rv.down = .loc l₂.down ⌟ ∗ (⌞ r = .unit ⌟ ∗ l₂.down ↦∅))
          (by simp [dropCtx₁, dropSpecFreed, SpecCtx.update_apply])))
    · rintro ⟨l₂, l₁, v, rv, ts⟩ h ⟨ha, h₂, rfl, d, hA, hrest⟩
      obtain ⟨hrv, hpt₂⟩ := hPure_star_elim hrest
      obtain ⟨h₁, hop, rfl, d1o, hpt₁, hopP⟩ := hA
      obtain ⟨d12, dop2⟩ := PFun.disjoint_union_left.mp d
      rw [PFun.union_comm d]
      exact hPure_star_intro rfl (hPure_star_intro hrv
        (hProp_star_star_intro hpt₂ hpt₁ hopP d12.symm dop2.symm d1o))
    · rintro r ⟨l₂, l₁, v, rv, ts⟩ h hh
      obtain ⟨hrv, hh⟩ := hPure_star_elim hh
      obtain ⟨hr, hh⟩ := hPure_star_elim hh
      obtain ⟨h₂, h₁, hop, rfl, d21, d2o, d1o, hpt₂, hpt₁, hopP⟩ := hProp_star_star_elim hh
      rw [PFun.union_comm (PFun.disjoint_union_right.mpr ⟨d21, d2o⟩)]
      exact ⟨h₁ ∪ hop, h₂, rfl, PFun.disjoint_union_left.mpr ⟨d21.symm, d2o.symm⟩,
        ⟨h₁, hop, rfl, d1o, hpt₁, hopP⟩, hPure_star_intro hrv (hPure_star_intro hr hpt₂)⟩
  -- the body of the recursive branch: free the head cell, then recurse on it
  have Dk : dropCtx₁ τ ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val) (rv : Lifted.{1} Val)
        (ts : TypedSubvariants.{0}),
      ⌈ ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₂.down ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉
      (Expr.letIn .anon (.free (.val rv.down))
        (.call "drop" [τ ts] [.val rv.down]))
      ⌈ .lerr : λₗ r, ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ r = .unit ⌟ ∗ (l₂.down ↦∅ ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉ :=
    .letIn (tt := bTele₂) (x := .anon) (v := fun _ _ _ _ _ => ULift.up Val.unit)
      (e₁ := fun _ _ _ rv _ => ULift.up (Expr.free (.val rv.down)))
      (e₂ := fun _ _ _ rv ts => ULift.up (Expr.call "drop" [τ ts] [.val rv.down]))
      Dfree Dcall
  -- the value read is a pointer, so the glue takes its recursive branch
  have Dmain : dropCtx₁ τ ⊢ λₗ (l₂ : Lifted.{1} Loc) (l₁ : Lifted.{1} Loc) (v : Lifted.{1} Val) (rv : Lifted.{1} Val)
        (ts : TypedSubvariants.{0}),
      ⌈ ⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₂.down ∗ (l₁.down ↦ v.down ∗ A v.down ts)) ⌉
      (Expr.letIn (.named "v") (.load (.val rv.down))
        (.choice
          (.letIn (.named "g") (.pure (isUnitTest (.var "v")))
            (.letIn .anon (.assume (.var "g")) .unit))
          (.letIn (.named "g") (.pure (.not (isUnitTest (.var "v"))))
            (.letIn .anon (.assume (.var "g"))
              (.letIn .anon (.free (.val rv.down)) (.call "drop" [τ ts] [.var "v"]))))))
      ⌈ .lerr : λₗ r, ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ r = .unit ⌟ ∗ (l₂.down ↦∅ ∗ (l₁.down ↦ v.down ∗ A v.down ts))) ⌉ :=
    .letIn (tt := bTele₂) (x := .named "v") (v := fun _ _ _ rv _ => rv)
      (e₁ := fun _ _ _ rv _ => ULift.up (Expr.load (.val rv.down)))
      (e₂ := fun _ _ _ rv ts => ULift.up (Expr.choice
        (.letIn (.named "g") (.pure (isUnitTest (.var "v")))
          (.letIn .anon (.assume (.var "g")) .unit))
        (.letIn (.named "g") (.pure (.not (isUnitTest (.var "v"))))
          (.letIn .anon (.assume (.var "g"))
            (.letIn .anon (.free (.val rv.down)) (.call "drop" [τ ts] [.var "v"]))))))
      Dload
      (wfSpec_not_isUnitTest_branch
        (P := fun ⟨l₂, l₁, v, rv, ts, _⟩ => ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ rv.down = .loc l₂.down ⌟ ∗ (l₂.down ↦ .loc l₂.down ∗ (l₁.down ↦ v.down ∗ A v.down ts))))
        (Φ := fun r ⟨l₂, l₁, v, rv, ts, _⟩ => ⌞ rv.down = .loc l₂.down ⌟ ∗
          (⌞ r = .unit ⌟ ∗ (l₂.down ↦∅ ∗ (l₁.down ↦ v.down ∗ A v.down ts))))
        (w := fun ⟨_, _, _, rv, _, _⟩ => rv.down)
        (e₁ := fun ⟨_, _, _, rv, _, _⟩ => Expr.letIn (.named "g")
          (.pure (isUnitTest (.val rv.down))) (.letIn .anon (.assume (.var "g")) .unit))
        (k := fun ⟨_, _, _, rv, ts, _⟩ => Expr.letIn .anon (.free (.val rv.down))
          (.call "drop" [τ ts] [.val rv.down]))
        -- the value read out of the box is the head pointer, so the guard is `true`
        (by
          rintro ⟨l₂, l₁, v, rv, ts, ⟨⟩⟩ h hh
          obtain ⟨hrv, -⟩ := hPure_star_elim hh
          dsimp only
          rw [show rv.down = Val.loc l₂.down from hrv]
          exact eval_not_isUnitTest_loc l₂.down)
        (fun _ => rfl) Dk)
  -- strip the trailing `emp`
  refine .cons (tt := bTele₂) id (fun _ => List.Subset.refl _) ?_ ?_ (fun _ => rfl) Dmain
  · exact fun _ _ hh => hProp_star_emp_intro hh
  · exact fun _ _ _ hh => hh

/-! The fresh program variables `PVar.freshen` generates for the four let-bound sources. -/

private def boxFresh₁ : PVar := "xxxxxxxxxxxxxxxxxxxxxxx.xxxxxxxxxxx.xxxxx.xx.x"
private def boxFresh₂ : PVar := "xxxxxxxxxxx.xxxxx.xx.x"
private def boxFresh₃ : PVar := "xxxxx.xx.x"
private def boxFresh₄ : PVar := "xx.x"

/-- The main program exhibiting the use-after-free: `drop(cycle(rebox(box(unit))))`, in
let-normal form.  Every call is instantiated at the unit type, and each stage let-binds its
result to the parameter `x` of the next one. -/
def boxSourceExpr : Expr :=
  .letIn (.named boxFresh₁) (.pure (.val .unit))
    (.letIn (.named "x")
      (.letIn (.named boxFresh₂) (.pure (.var boxFresh₁))
        (.letIn (.named "x")
          (.letIn (.named boxFresh₃) (.pure (.var boxFresh₂))
            (.letIn (.named "x")
              (.letIn (.named boxFresh₄) (.pure (.var boxFresh₃))
                (.letIn (.named "x")
                  (.letIn (.named "x") (.pure (.var boxFresh₄)) (.pure (.var "x")))
                  (.call "box" [.unit] [.var "x"])))
              (.call "rebox" [.unit] [.var "x"])))
          (.call "cycle" [.unit] [.var "x"])))
      (.call "drop" [.unit] [.var "x"]))

/-- `boxSourceExpr` is the witness program of the source derived for `drop`, at the picks
describing the unit type by the summary of unit values. -/
theorem boxSourceExpr_eq_witness :
    boxSourceExpr = (dropDecl.callSource "drop" ςsDrop).witness
      (TypePicks.unit (dropDecl.callSource "drop" ςsDrop)) PUnit.unit := rfl

/-- The simplified postcondition of `drop` is satisfiable at any typed subvariant and any
input value owning an inhabitant of it in a finite state: the input value is boxed twice,
with the outer cell pointing to itself and then freed. -/
theorem dropSubv_satAt {ts : TypedSubvariants.{0}} {v : Val} {h : Heap}
    (hfin : h.dom.Finite) (hown : HProp h (ts.get boxLib 0 v)) :
    Sat (dropSumm.ownedAt Val.unit (TeleArg.app PUnit.unit ⟨v, PUnit.unit⟩)
      ⟨ts, PUnit.unit⟩) := by
  obtain ⟨b₁, b₂, hne, hb₁, hb₂⟩ := exists_two_fresh_blocks hfin
  have hd₁ : blockOf b₁ v ##ₘ h :=
    PFun.disjoint_insert_left.mpr ⟨hb₁, PFun.disjoint_empty_left h⟩
  have hd₂ : freedOf b₂ ##ₘ (blockOf b₁ v ∪ h) :=
    PFun.disjoint_union_right.mpr
      ⟨PFun.disjoint_insert_left.mpr
          ⟨by simp [blockOf, PFun.singleton, Ne.symm hne], PFun.disjoint_empty_left _⟩,
        PFun.disjoint_insert_left.mpr ⟨hb₂, PFun.disjoint_empty_left h⟩⟩
  refine ⟨freedOf b₂ ∪ (blockOf b₁ v ∪ h), ?_⟩
  show HProp _ ((dropDecl.summary "drop" ςsDrop dropSubv).ownedAt Val.unit
    (TeleArg.app PUnit.unit ⟨v, PUnit.unit⟩) ⟨ts, PUnit.unit⟩)
  rw [FunDecl.hProp_summary_ownedAt dropDecl "drop" ςsDrop dropSubv]
  exact ⟨(b₁, 0), (b₂, 0), ∅, _, (PFun.empty_union _).symm, PFun.disjoint_empty_left _,
    ⟨rfl, rfl⟩, freedOf b₂, blockOf b₁ v ∪ h, rfl, hd₂,
    hProp_freedOf b₂, blockOf b₁ v, h, rfl, hd₁, hProp_blockOf b₁ v, hown⟩

/-- The picks for `drop` are summaries of the type space `cycleCtx`, fitting its parameters. -/
theorem safePicks_drop : dropDecl.SafePicks cycleCtx ςsDrop := by
  refine ⟨by decide, ?_⟩
  rintro ⟨τ, ς⟩ h
  simp only [ςsDrop, List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [cycleCtx, SummCtx.update, SummCtx.MemTy]

theorem tryRefute_drop : boxLib.TryRefute risl semSolver cycleCtx (.inr boxSourceExpr) := by
  refine ⟨"drop", dropDecl, boxLib_drop, rfl, ςsDrop, safePicks_drop,
    .lerr, dropPost, ?derivPost, dropSubv, dropPost_simplifiesTo,
    ?satPost,
    by simp, TypePicks.unit (dropDecl.callSource "drop" ςsDrop), ?picksOk,
    TeleArg.uliftArg PUnit.unit,
    ?witSat, rfl⟩
  case picksOk =>
    -- the unit type is described by the summary of unit values, which the type space holds
    exact TypePicks.unit_safe (SummCtx.mem_update_of_mem
      (SummCtx.mem_update_of_mem (SummCtx.mem_update_of_mem (base_mem_unit boxLib))))
  case witSat =>
    refine semSolver_model_typedSymAsrt.mpr ?_
    rw [TeleArg.ulower_uliftArg]
    refine ⟨Val.unit, ⟨Val.unit, PUnit.unit⟩, dropSubv_satAt (h := ∅) (by simp) ?_⟩
    exact ⟨rfl, rfl⟩
  case satPost =>
    refine (semSolver_sat_owned_symAsrt (ς := dropSumm)).mpr ?_
    exact ⟨⟨Val.unit, PUnit.unit⟩, ⟨Ty.unit, PUnit.unit⟩, Val.unit,
      dropSubv_satAt (hProp_opaque_finite (hProp_empty_opaque_unit.{0} boxLib))
        (hProp_empty_get_default boxLib 0)⟩
  case derivPost =>
    refine ⟨SpecCtx.fromPicks ςsDrop "drop" boxLib dropDecl.tyArity .lerr dropPost
        (dropCtx₁ fun ts => ts.ty),
      ⟨.update (tt := ςsDrop.callTele 1) (φ := dropDecl) (tys := ςsDrop.callTyArgs 1)
          (vals := ςsDrop.callValArgs boxLib 1)
          (wfSpecCtx_dropCtx₁ _) rfl boxLib_drop ?bodyTriple,
        ?callRule⟩⟩
    case callRule =>
      exact wfSpec_mergeCall ςsDrop "drop" boxLib dropDecl.tyArity .lerr dropPost
        (by simp [SpecCtx.update_apply])
    case bodyTriple =>
      refine .cons (tt := ςsDrop.callTele 1) (tt' := ςsDrop.callTele 1) id
        (fun _ => List.Subset.refl _) ?pre (fun _ _ _ hh => hh) (fun _ => rfl)
        (.ex (tt := ςsDrop.callTele 1) (X := Loc)
          (e := fun _ rv ts => ULift.up (Expr.letIn (.named "v") (.load (.val rv.down))
            (.choice
              (.letIn (.named "g") (.pure (isUnitTest (.var "v")))
                (.letIn .anon (.assume (.var "g")) .unit))
              (.letIn (.named "g") (.pure (.not (isUnitTest (.var "v"))))
                (.letIn .anon (.assume (.var "g"))
                  (.letIn .anon (.free (.val rv.down))
                    (.call "drop" [ts.ty] [.var "v"])))))))
          (.ex (tt := bTele) (X := Loc)
            (e := fun _ _ rv ts => ULift.up (Expr.letIn (.named "v") (.load (.val rv.down))
              (.choice
                (.letIn (.named "g") (.pure (isUnitTest (.var "v")))
                  (.letIn .anon (.assume (.var "g")) .unit))
                (.letIn (.named "g") (.pure (.not (isUnitTest (.var "v"))))
                  (.letIn .anon (.assume (.var "g"))
                    (.letIn .anon (.free (.val rv.down))
                      (.call "drop" [ts.ty] [.var "v"])))))))
            (wfSpec_dropBody (fun ts => ts.ty)
              (fun v ts => ts.get boxLib 0 v))))
      case pre =>
        rintro ⟨v, rv, ts, ⟨⟩⟩ h ⟨l₁, l₂, hh⟩
        simp only [polyAsrt_apply, Picks.mergeOwned, ςsDrop, Picks.merge_cons,
          cycleSumm]
        refine (hProp_star_congr_left fun _ =>
          FunDecl.hProp_summary_ownedAt cycleDecl "cycle" ςsCycle cycleSubv
            _ _ _).mpr ?_
        rw [cycleSubv_at_congr (T := ⟨ts, PUnit.unit⟩)]
        · exact hProp_star_emp_intro ⟨l₁, l₂, hProp_star_emp_elim hh⟩
        · exact fun w => by rw [Picks.headSubvs_get_param _ _ _ _ (by decide) (by decide)]; rfl

/-! ### Well-formed summary context and inadequacy -/

/-- The type space `cycleCtx` is well formed: it is reached from the base one by the three
derivation steps above. -/
theorem wfSummCtx_cycleCtx : WfSummCtx risl semSolver boxLib cycleCtx :=
  ((WfSummCtx.base.infer tryRefute_box).infer tryRefute_rebox).infer tryRefute_cycle

/-- The refutation of the unit type constructor in the `Box` library. -/
theorem hasRefutedType_boxSourceExpr : boxLib.HasRefutedType boxSourceExpr :=
  ⟨risl, risl_sound, cycleCtx, wfSummCtx_cycleCtx, tryRefute_drop⟩

/-- **The `Box` library is inadequate**: `drop(cycle(rebox(box(unit))))` is a well-typed
main program whose execution reads an already freed cell of the cyclic box. -/
theorem box_inadequate : boxLib.Inadequate boxSourceExpr :=
  inadequacy hasRefutedType_boxSourceExpr

end RUXt
