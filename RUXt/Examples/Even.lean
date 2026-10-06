import RUXt.Semantics.Inadequacy
import RUXt.Examples.Calls

namespace RUXt

/-!
# The `Even` library and its type unsoundness

This file formalises a small (unsound) Rust library for even numbers and shows, via
the refutation algorithm of `RUXt/Model/Refute.lean`, that the library is *inadequate*:
it has a well-typed main program whose execution exhibits undefined behaviour. -/

/-- The custom struct type `Even`. -/
abbrev Ty.even : Ty := .custom "Even" []
abbrev TyConsId.even : TyConsId := .custom "Even" []

@[simp] theorem TyConsId.arity_even : TyConsId.even.arity = 0 := rfl

abbrev newBody : Expr :=
  .pure ((Pure.var "z").add ((Pure.var "z").mod (.int 2)).minus)
/-- Creates an even number from an integer. -/
def newDecl : FunDecl := ⟨0, ⟨[("z", .int)], fun ⟨⟩ ⟨⟩ => newBody, .even, true⟩⟩
def newImpl : FunImpl := newDecl.concretise .unit

abbrev succBody : Expr :=
  .pure ((Pure.var "x").add (.int 1))
/-- Increments its input number. -/
def succDecl : FunDecl := ⟨0, ⟨[("x", .even)], fun ⟨⟩ ⟨⟩ => succBody, .even, true⟩⟩
def succImpl : FunImpl := succDecl.concretise .unit

abbrev nextBody : Expr :=
  .letIn (.named "x") (.call "succ" [] [.var "x"]) (.call "succ" [] [.var "x"])
/-- Computes the next even number. -/
def nextDecl : FunDecl := ⟨0, ⟨[("x", .even)], fun ⟨⟩ ⟨⟩ => nextBody, .even, true⟩⟩
def nextImpl : FunImpl := nextDecl.concretise .unit

abbrev isEven (p : Pure) : Pure :=
  (p.mod (.int 2)).eq (.int 0)
abbrev noopBody : Expr := .choice
  (.letIn (.named "g") (.pure (isEven (.var "x")))
    (.letIn .anon (.assume (.var "g")) .unit))
  (.letIn (.named "g") (.pure (.not (isEven (.var "x"))))
    (.letIn .anon (.assume (.var "g")) .error))
/-- Performs no operation on even inputs, exhibits UB on odd inputs. -/
def noopDecl : FunDecl := ⟨0, ⟨[("x", .even)], fun ⟨⟩ ⟨⟩ => noopBody, .unit, true⟩⟩
def noopImpl : FunImpl := noopDecl.concretise .unit

/-- The `Even` library. -/
def evenLib : Library where
  implementations := fun f =>
    if f = "new" then newDecl
    else if f = "succ" then succDecl
    else if f = "next" then nextDecl
    else if f = "noop" then noopDecl
    else Part.none
  paramsValid := by
    intro f φ hφ; split_ifs at hφ <;> simp at hφ <;> subst hφ <;>
      exact ⟨by simp [FunDecl.ParamsNodup, FunDecl.paramNames, FunTempl.paramNames,
          newDecl, succDecl, nextDecl, noopDecl],
        by decide⟩
  tyParamsOrdered := by
    intro f φ hφ; split_ifs at hφ <;> simp at hφ <;> subst hφ <;> decide

theorem evenLib_new : evenLib.MapsTo "new" newDecl := by
  simp [Library.MapsTo, evenLib]
theorem evenLib_succ : evenLib.MapsTo "succ" succDecl := by
  simp [Library.MapsTo, evenLib]
theorem evenLib_next : evenLib.MapsTo "next" nextDecl := by
  simp [Library.MapsTo, evenLib]
theorem evenLib_noop : evenLib.MapsTo "noop" noopDecl := by
  simp [Library.MapsTo, evenLib]

theorem evenLib_inst_new : evenLib.Instantiates "new" [] newImpl :=
  evenLib.instantiates_concretise evenLib_new .unit
theorem evenLib_inst_succ : evenLib.Instantiates "succ" [] succImpl :=
  evenLib.instantiates_concretise evenLib_succ .unit
theorem evenLib_inst_next : evenLib.Instantiates "next" [] nextImpl :=
  evenLib.instantiates_concretise evenLib_next .unit
theorem evenLib_inst_noop : evenLib.Instantiates "noop" [] noopImpl :=
  evenLib.instantiates_concretise evenLib_noop .unit

/-! ### Iteration 1 of the refutation procedure: `new` Ok execution -/

/-- Picks for `new`: the base `int` summary. -/
def ςs1 : Picks := [(.int, Summary.base .int)]
/-- The postcondition obtained from executing the `new` function. -/
def evenPost : ςs1.DerivedPost 0 :=
  fun r ⟨z, v, ⟨⟩⟩ => ⌞ v.down = .int z.down ⌟ ∗
  ⌞ some r = ((Pure.val v.down).add ((Pure.val v.down).mod (.int 2)).minus).eval ⌟
/-- Simplified evenPost: `new` maps `.int z` to the even `.int (z-z%2)`. -/
def evenSubv : newDecl.Subvariant ςs1 :=
  fun r ⟨z, ⟨⟩⟩ => ⌞ r = .int (z.down - z.down.tmod 2) ⌟

theorem evenPost_simplifiesTo : evenPost.SimplifiesTo semSolver evenSubv :=
  semSolver_simplifiesTo.mpr <| by
    rintro r ⟨z, ⟨⟩⟩ ⟨⟩ h
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨.int z, .unit⟩, ⟨∅, ∅, by simp, by simp, ⟨rfl, rfl⟩,
      ⟨rfl, by simp [Pure.eval, UnOp.eval, BinOp.eval, TeleArg.app, TeleArg.uliftArg,
        Int.sub_eq_add_neg]⟩⟩⟩
    · rintro ⟨⟨v, ⟨⟩⟩, hh⟩
      obtain ⟨_, _, rfl, -, ⟨rfl, hv⟩, ⟨rfl, hr⟩⟩ := hh
      obtain rfl : v = .int z := hv
      simp only [Pure.eval, Term.eval_val, UnOp.eval, BinOp.eval,
        TeleArg.app, TeleArg.uliftArg, Option.some.injEq] at hr
      exact ⟨by simp, hr⟩

/-- The (correct) summary for `Even`, obtained from `new`. -/
def evenSumm : Summary := newDecl.summary "new" ςs1 evenSubv
/-- Context after adding the even summary. -/
def evenCtx : SummCtx := SummCtx.update (SummCtx.base evenLib) .even evenSumm

theorem tryRefute_even : evenLib.TryRefute risl semSolver (SummCtx.base evenLib) (.inl (.even, evenSumm)) := by
  refine ⟨"new", newDecl, evenLib_new, rfl, ςs1, ⟨by decide, ?summIncl⟩,
    .lok, evenPost, ?derivPost, evenSubv, evenPost_simplifiesTo,
    ?satPost, rfl, rfl⟩
  case summIncl =>
    rintro ⟨τ, ς⟩ h
    simp only [ςs1, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [SummCtx.base, SummCtx.update, SummCtx.MemTy]
  case satPost =>
    refine (semSolver_sat_owned_symAsrt (ς := newDecl.summary "new" ςs1 evenSubv)).mpr ?_
    refine ⟨⟨0, .unit⟩, PUnit.unit, .int (0 - Int.tmod 0 2), ∅, ?_⟩
    rw [FunDecl.hProp_summary_ownedAt newDecl "new" ςs1 evenSubv]
    exact ⟨rfl, rfl⟩
  case derivPost =>
    -- Select RISL as our logic for executing the function call
    refine ⟨SpecCtx.fromPicks ςs1 "new" newDecl.arity .lok evenPost,
      ⟨.update (φ := newDecl) (tys := ςs1.callTyArgs 0) (vals := ςs1.callValArgs 0)
        .empty rfl evenLib_new ?_, ?_⟩⟩
    -- Prove triple for the function body
    · refine .cons id (fun _ => List.Subset.refl _) ?pre (fun _ _ _ h => h)
        (fun _ => rfl)
        -- Frame .int equality
        (.frame (tt := ςs1.callTele 0)
          (R := fun ⟨z, v, _⟩ => ⌞ v.down = .int z.down ⌟)
        -- Evaluate modulo operation as a pure expression
        (.reindex (tt := [tele (_ : Lifted.{1} Pure)]) (tt' := ςs1.callTele 0)
          (fun ⟨_, v, _⟩ =>
            ⟨.up ((Pure.val v.down).add ((Pure.val v.down).mod (.int 2)).minus), .unit⟩)
          .pure))
      intro args
      simp only [polyAsrt_apply, Picks.mergeOwned, ςs1, Picks.merge_cons,
        HValid, hProp_implies, hProp_star, Summary.base_ownedAt_int]
      exact fun _ h => h
    -- The merged call is an instance of the `call` rule
    · exact wfSpec_mergeCall ςs1 "new" newDecl.arity .lok evenPost
        (by simp [SpecCtx.update_apply])

/-! ### Iteration 2 of the refutation procedure: `succ` Ok execution -/

/-- Picks for `succ`: the even `Even` summary. -/
def ςs2 : Picks := [(.even, evenSumm)]
/-- The postcondition obtained from executing the `succ` function. -/
def oddPost : ςs2.DerivedPost 0 :=
  fun r ⟨z, v, ⟨⟩⟩ => evenSubv v.down ⟨z, .unit⟩ ∗
  ⌞ some r = ((Pure.val v.down).add (.int 1)).eval ⌟
/-- Simplified oddPost: `succ` maps the even `.int (z-z%2)` to the odd `.int ((z-z%2)+1)`. -/
def oddSubv : succDecl.Subvariant ςs2 :=
  fun r ⟨z, ⟨⟩⟩ => ⌞ r = .int (z.down - z.down.tmod 2 + 1) ⌟

theorem oddPost_simplifiesTo : oddPost.SimplifiesTo semSolver oddSubv :=
  semSolver_simplifiesTo.mpr <| by
    rintro r ⟨z, ⟨⟩⟩ ⟨⟩ h
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨.int (z - z.tmod 2), .unit⟩,
        ⟨∅, ∅, by simp, by simp, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
    · rintro ⟨⟨v, ⟨⟩⟩, hh⟩
      obtain ⟨_, _, rfl, -, ⟨rfl, hv⟩, ⟨rfl, hr⟩⟩ := hh
      obtain rfl : v = .int (z - z.tmod 2) := hv
      simp only [Pure.eval, Term.eval_val, BinOp.eval,
        TeleArg.app, TeleArg.uliftArg, Option.some.injEq] at hr
      exact ⟨by simp, hr⟩

/-- The *unsound* odd summary for `Even`, obtained from `succ`. -/
def oddSumm : Summary := succDecl.summary "succ" ςs2 oddSubv
/-- Context after adding the odd summary. -/
def oddCtx : SummCtx := SummCtx.update evenCtx .even oddSumm

theorem tryRefute_odd : evenLib.TryRefute risl semSolver evenCtx (.inl (.even, oddSumm)) := by
  refine ⟨"succ", succDecl, evenLib_succ, rfl, ςs2, ⟨by decide, ?summIncl⟩,
    .lok, oddPost, ?derivPost, oddSubv, oddPost_simplifiesTo,
    ?satPost, rfl, rfl⟩
  case summIncl =>
    rintro ⟨τ, ς⟩ h
    simp only [ςs2, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [evenCtx, SummCtx.update, SummCtx.MemTy]
  case satPost =>
    refine (semSolver_sat_owned_symAsrt (ς := succDecl.summary "succ" ςs2 oddSubv)).mpr ?_
    refine ⟨⟨0, .unit⟩, PUnit.unit, .int (0 - Int.tmod 0 2 + 1), ∅, ?_⟩
    rw [FunDecl.hProp_summary_ownedAt succDecl "succ" ςs2 oddSubv]
    exact ⟨rfl, rfl⟩
  case derivPost =>
    -- Select RISL as our logic for executing the function call
    refine ⟨SpecCtx.fromPicks ςs2 "succ" succDecl.arity .lok oddPost,
      ⟨.update (φ := succDecl) (tys := ςs2.callTyArgs 0) (vals := ςs2.callValArgs 0)
        .empty rfl evenLib_succ ?_, ?_⟩⟩
    -- Prove triple for the function body
    · refine .cons id (fun _ => List.Subset.refl _) ?pre (fun _ _ _ h => h)
        (fun _ => rfl)
        -- Frame the resources of the picked summary
        (.frame (tt := ςs2.callTele 0)
          (R := fun ⟨z, v, _⟩ => evenSubv v.down ⟨z, PUnit.unit⟩)
        -- Evaluate increment as a pure expression
        (.reindex (tt := [tele (_ : Lifted.{1} Pure)]) (tt' := ςs2.callTele 0)
          (fun ⟨_, v, _⟩ => ⟨.up ((Pure.val v.down).add (.int 1)), .unit⟩) .pure))
      intro args
      simp only [polyAsrt_apply, Picks.mergeOwned, ςs2, Picks.merge_cons,
        evenSumm]
      rintro _ ⟨h₁, h₂, rfl, hd, hp, hq⟩
      exact ⟨h₁, h₂, rfl, hd,
        (FunDecl.hProp_summary_ownedAt newDecl "new" ςs1 evenSubv
          _ _ _).mpr hp, hq⟩
    -- The merged call is an instance of the `call` rule
    · exact wfSpec_mergeCall ςs2 "succ" succDecl.arity .lok oddPost
        (by simp [SpecCtx.update_apply])

/-! ### Iteration 3 of the refutation procedure: `noop` Err execution -/

/-- Picks for `noop`: the odd `Even` summary. -/
def ςs3 : Picks := [(.even, oddSumm)]
/-- The postcondition obtained from executing the `noop` function. -/
def noopPost : ςs3.DerivedPost 0 :=
  fun r ⟨z, v, ⟨⟩⟩ => oddSubv v.down ⟨z, .unit⟩ ∗
  ⌞ some (.bool true) = (isEven (.val v.down)).not.eval ⌟ ∗ ⌞ r = .unit ⌟
/-- Simplified noopPost: it reaches an error state for the odd input `.int ((z-z%2)+1)`, returning .unit -/
def noopSubv : noopDecl.Subvariant ςs3 :=
  fun r _ => ⌞ r = .unit ⌟
/-- The program exhibiting UB: `noop(succ(new(0)))` in let-normal form. -/
def sourceExpr : Expr :=
  .letIn (.named "x") (.letIn (.named "x") (.letIn (.named "z") (.int 0)
    (.call "new" [] [.var "z"])) (.call "succ" [] [.var "x"])) (.call "noop" [] [.var "x"])

theorem noopPost_simplifiesTo : noopPost.SimplifiesTo semSolver noopSubv :=
  semSolver_simplifiesTo.mpr <| by
    rintro r ⟨z, ⟨⟩⟩ ⟨⟩ h
    constructor
    · rintro ⟨rfl, rfl⟩
      refine ⟨⟨.int (z - z.tmod 2 + 1), .unit⟩,
        ∅, ∅, by simp, by simp, ⟨rfl, rfl⟩,
        ⟨∅, ∅, by simp, by simp, ⟨rfl, ?_⟩, ⟨rfl, rfl⟩⟩⟩
      simp [Pure.eval, UnOp.eval, BinOp.eval, TeleArg.app, TeleArg.uliftArg]
      rw [← Int.dvd_iff_tmod_eq_zero]
      have := Int.mul_tdiv_add_tmod z 2
      omega
    · rintro ⟨⟨_, ⟨⟩⟩, -, _, rfl, -, ⟨rfl, -⟩, ⟨-, -, rfl, -, ⟨rfl, -⟩, ⟨rfl, hr⟩⟩⟩
      exact ⟨by simp, hr⟩

/-- The picks for `noop` are summaries of the type space `oddCtx`, fitting its parameters. -/
theorem safePicks_noop : noopDecl.SafePicks oddCtx ςs3 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨τ, ς⟩ h
  simp only [ςs3, List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [oddCtx, SummCtx.update, SummCtx.MemTy]

theorem tryRefute_noop : evenLib.TryRefute risl semSolver oddCtx (.inr sourceExpr) := by
  refine ⟨"noop", noopDecl, evenLib_noop, rfl, ςs3, safePicks_noop,
    .lerr, noopPost, ?derivPost, noopSubv, noopPost_simplifiesTo,
    ?satPost,
    by simp, TypePicks.unit (noopDecl.callSource "noop" ςs3), ?picksOk,
    TeleArg.uliftArg ⟨0, PUnit.unit⟩, ?witSat, rfl⟩
  case picksOk =>
    -- the unit type is described by the summary of unit values, which the type space holds
    exact TypePicks.unit_safe
      (SummCtx.mem_update_of_mem (SummCtx.mem_update_of_mem (base_mem_unit evenLib)))
  case witSat =>
    refine semSolver_model_typedSymAsrt.mpr ?_
    rw [TeleArg.ulower_uliftArg]
    exact ⟨Val.unit, PUnit.unit, ∅, rfl, rfl⟩
  case satPost =>
    refine (semSolver_sat_owned_symAsrt (ς := noopDecl.summary "noop" ςs3 noopSubv)).mpr ?_
    refine ⟨⟨0, .unit⟩, PUnit.unit, .unit, ∅, ?_⟩
    rw [FunDecl.hProp_summary_ownedAt noopDecl "noop" ςs3 noopSubv]
    exact ⟨rfl, rfl⟩
  case derivPost =>
    -- Select RISL as our logic for executing the function call
    refine ⟨SpecCtx.fromPicks ςs3 "noop" noopDecl.arity .lerr noopPost,
      ⟨.update (φ := noopDecl) (tys := ςs3.callTyArgs 0) (vals := ςs3.callValArgs 0)
        .empty rfl evenLib_noop ?_, ?_⟩⟩
    -- Prove triple for the function body
    · refine .cons id (fun _ => List.Subset.refl _) ?pre (fun _ _ _ h => h)
        (fun _ => rfl) (
        -- Choose the error branch
        .choice (tt := ςs3.callTele 0)
          (e₁ := fun ⟨_, v, _⟩ => .letIn (.named "g") (.pure (isEven (.val v.down)))
            (.letIn .anon (.assume (.var "g")) .unit))
          (e₂ := fun ⟨_, v, _⟩ => .letIn (.named "g") (.pure (.not (isEven (.val v.down))))
            (.letIn .anon (.assume (.var "g")) .error))
          (Or.inr rfl)
        -- Frame .int equality
        (.frame (tt := ςs3.callTele 0)
          (R := fun ⟨z, v, _⟩ => oddSubv v.down ⟨z, PUnit.unit⟩)
          (Φ := fun r ⟨_, v, _⟩ =>
            ⌞ some (.bool true) = (isEven (.val v.down)).not.eval ⌟ ∗ ⌞ r = .unit ⌟)
        -- Evaluate let-binding for the guard
        (.letIn (tt := ςs3.callTele 0) (v := fun _ => (.bool true))
          (e₂ := fun _ => (.letIn .anon (.assume (.var "g")) .error))
        -- Evaluate guard as a pure expression
        (.reindex (tt := [tele (_ : Lifted.{1} Pure)]) (tt' := ςs3.callTele 0)
          (fun ⟨_, v, _⟩ => ⟨.up (.not (isEven (.val v.down))), .unit⟩) .pure)
        -- Add .emp to precondition for framing
        (.cons id (fun _ => List.Subset.refl _)
          ?consEmp (fun _ _ _ hh => hh) (fun _ => rfl)
        -- Frame the guard evaluation
        (.frame (tt := ςs3.callTele 0)
          (R := fun ⟨_, v, _⟩ =>
            ⌞ some (.bool true) = (isEven (.val v.down)).not.eval ⌟)
        -- Evaluate let-binding for assume
        (.letIn (tt := ςs3.callTele 0) (x := .anon) (v := fun _ => .unit)
          (e₂ := fun _ => .error)
        -- Evaluate assume
        (.reindex (tt := [tele]) (fun _ => .unit) .assume)
        -- Remove unit equality from precondition
        (.cons id (fun _ => List.Subset.refl _)
          ?consUnit (fun _ _ _ hh => hh) (fun _ => rfl)
        -- Evaluate error
        (.reindex (tt := [tele]) (fun _ => .unit) .error))))))))
      case pre =>
        intro args
        simp only [polyAsrt_apply, Picks.mergeOwned, ςs3, Picks.merge_cons,
          oddSumm]
        rintro _ ⟨h₁, h₂, rfl, hd, hp, hq⟩
        exact ⟨h₁, h₂, rfl, hd,
          (FunDecl.hProp_summary_ownedAt succDecl "succ" ςs2 oddSubv
            _ _ _).mpr hp, hq⟩
      case consEmp => exact fun _ => hValid_star_emp_left _
      case consUnit => exact fun _ _ hh => ⟨hh, rfl⟩
    -- The merged call is an instance of the `call` rule
    · exact wfSpec_mergeCall ςs3 "noop" noopDecl.arity .lerr noopPost
        (by simp [SpecCtx.update_apply])

/-! ### Well-formed summary context and inadequacy -/

/-- The type space `oddCtx` is well formed: it is reached from the base one by the two derivation
steps above. -/
theorem wfSummCtx_oddCtx : WfSummCtx risl semSolver evenLib oddCtx :=
  (WfSummCtx.base.infer tryRefute_even).infer tryRefute_odd

/-- The refutation of the unit type constructor in the `Even` library. -/
theorem hasRefutedType_sourceExpr : evenLib.HasRefutedType sourceExpr :=
  ⟨risl, risl_sound, oddCtx, wfSummCtx_oddCtx, tryRefute_noop⟩

/-- **The `Even` library is inadequate**: `noop(succ(new(0)))` is a well-typed
main program that exhibits undefined behaviour. -/
theorem even_inadequate : evenLib.Inadequate sourceExpr :=
  inadequacy hasRefutedType_sourceExpr

end RUXt
