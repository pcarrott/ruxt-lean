import RUXt.Model.Refute
import RUXt.Semantics.Summary.Derive
import RUXt.Semantics.Summary.Specialise
import RUXt.Semantics.Witness

/-!
# Adequacy of the refutation algorithm

What a refutation claims (`Library.HasRefutedType`, `Library.Inadequate`), examples of the
specialisation rule firing, validity of well-formed type spaces (`summCtx_soundness`), and the
adequacy result `inadequacy`: a refuted type assignment is inadequate.
-/

namespace RUXt

/-! ### What a refutation claims -/

/-- A type assignment in the library can be refuted: the refutation is carried out in some
**sound** program logic `L` (`Logic.Sound`), which is all a refutation is worth. -/
def Library.HasRefutedType (Λ : Library) (e : Expr) : Prop :=
  ∃ L : Logic.{0}, L.Sound ∧
    ∃ S, WfSummCtx L semSolver Λ S ∧ ∃ τ, Λ.TryRefute L semSolver S τ (.inr e)
/-- A main program exhibits undefined behaviour. -/
def Library.Inadequate (Λ : Library) (e : Expr) : Prop :=
  ∃ τ, SafeMain Λ τ e ∧ ∃ h, Λ ⊢ ⟨∅ | e⟩ ⇓ ⟨h | .err⟩
/-! ## Properties

### The specialisation rule can fire

The rule is not vacuous: the identity summary of the base type space can be specialised at
the unit type, described by the summary of unit values, and the resulting summary — an
inhabitant of the unit type constructor — extends the base type space to a well-formed
one.  Nor is it restricted to concrete types: the identity summary can equally be specialised
at a type constructor using a type parameter of its own — the identity constructor, described
by the identity summary itself. -/

/-- The base type space contains the summary of unit values, filed for the unit type
constructor. -/
theorem base_mem_unit (Λ : Library) :
    (SummCtx.base Λ).MemTy (.base .unit) (Summary.base .unit) := by
  simp [SummCtx.base, SummCtx.MemTy, SummCtx.update, Function.update]

/-- The specialisation rule applies to the base type space: the type parameter of the
identity summary may be pinned to the unit type, described by the summary of unit
values. -/
theorem trySpecialise_id_unit (Λ : Library) :
    (SummCtx.base Λ).TrySpecialise semSolver .unit
      ((Summary.id Λ).specialise 0 .unit [Summary.base .unit]) := by
  refine ⟨Summary.id Λ, ⟨.param 0, SummCtx.mem_update_self _ _ _⟩, 0, Nat.zero_lt_one,
    .unit, [Summary.base .unit], ?_, rfl, rfl, rfl, ?_⟩
  case _ =>
    intro ς hς
    obtain rfl : ς = Summary.base .unit := by simpa using hς
    exact base_mem_unit Λ
  case _ =>
    -- Satisfiability of the specialised postcondition: the result and the value the let-bound
    -- source produces are the unit value, owning nothing.
    refine (semSolver_sat_owned_symAsrt
      (ς := (Summary.id Λ).specialise 0 .unit [Summary.base .unit])).mpr ?_
    refine ⟨TeleArg.app (TeleArg.app PUnit.unit (TeleArg.app PUnit.unit PUnit.unit))
      PUnit.unit, PUnit.unit, Val.unit, ∅, ?_⟩
    rw [Summary.specialise_ownedAt (TyConsId.anon_base .unit)]
    refine ⟨[Val.unit], ?_⟩
    simp only [SubvArgs.ownAssertions_cons, SubvArgs.ownAssertions_nil]
    rw [Summary.id_ownedAt]
    exact ⟨∅, ∅, by simp, by simp, ⟨rfl, rfl⟩,
      (Summary.base_ownedAt_unit _ _ _).mpr ⟨rfl, rfl⟩⟩

/-- Extending the base type space by that specialisation gives a well-formed type space. -/
theorem wfSummCtx_base_specialise_id_unit (L : Logic.{0}) (Λ : Library) :
    WfSummCtx L semSolver Λ ((SummCtx.base Λ).update .unit
      ((Summary.id Λ).specialise 0 .unit [Summary.base .unit])) :=
  .specialise .nil (trySpecialise_id_unit Λ)

/-- The specialisation rule applies at a type constructor with type parameters of its own: the
type parameter of the identity summary may be pinned to a type parameter `T` — the identity
constructor, which uses a type parameter — described by the identity summary itself, filed
for that constructor.  The type parameter of the pinned constructor becomes the type
parameter of the specialised summary, which inhabits the identity constructor again. -/
theorem trySpecialise_id_param (Λ : Library) :
    (SummCtx.base Λ).TrySpecialise semSolver (.param 0)
      ((Summary.id Λ).specialise 0 (.param 0) [Summary.id Λ]) := by
  refine ⟨Summary.id Λ, ⟨.param 0, SummCtx.mem_update_self _ _ _⟩, 0, Nat.zero_lt_one,
    .param 0, [Summary.id Λ], ?_, rfl, by rw [TyConsId.anon_param], rfl, ?_⟩
  case _ =>
    intro ς hς
    obtain rfl : ς = Summary.id Λ := by simpa using hς
    exact SummCtx.mem_update_self _ _ _
  case _ =>
    -- Satisfiability of the specialised postcondition, at the unit type: the result, the input
    -- value and the value the let-bound source produces are all the unit value, owning
    -- nothing but the opaque resource of the unit type.
    refine (semSolver_sat_owned_symAsrt
      (ς := (Summary.id Λ).specialise 0 (.param 0) [Summary.id Λ])).mpr ?_
    refine ⟨TeleArg.app (TeleArg.app PUnit.unit (TeleArg.app PUnit.unit PUnit.unit))
      (TeleArg.ofListPad Val.unit _ [Val.unit]), TeleArg.ofListPad Ty.unit _ [Ty.unit],
      Val.unit, ∅, ?_⟩
    rw [Summary.specialise_ownedAt (TyConsId.anon_param 0)]
    refine ⟨[Val.unit], ?_⟩
    simp only [SubvArgs.ownAssertions_cons, SubvArgs.ownAssertions_nil]
    rw [Summary.id_ownedAt]
    refine ⟨∅, ∅, by simp, by simp, ⟨rfl, rfl⟩, ?_⟩
    refine (TypedSubvariants.get_of_getElem? (ts := ⟨_, [_]⟩) (i := 0) rfl _).symm ▸ ?_
    rw [Summary.id_ownedAt]
    refine ⟨∅, ∅, by simp, by simp, ⟨rfl, rfl⟩, ?_⟩
    have hfst : ∀ {n : ℕ}
        (X : Σ _ : TypedSubvariants.{0}, TeleArg (Tele.uniform TypedSubvariants.{0} n)),
        X.1 = SubvArgs.get (n := n + 1) X 0 := fun _ => rfl
    erw [hfst, SubvArgs.get, TeleArg.toList_reindex_id _ _ rfl,
      TeleArg.toList_appendUniform, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [TeleArg.toList_length]; decide),
      ← List.getD_eq_getElem?_getD]
    show HProp ∅ ((SubvArgs.get _ 0).get Λ 0 _)
    rw [SubvArgs.get_block _ _ (by decide)]
    exact hProp_empty_opaque_unit Λ

/-- Extending the base type space by that specialisation gives a well-formed type space. -/
theorem wfSummCtx_base_specialise_id_param (L : Logic.{0}) (Λ : Library) :
    WfSummCtx L semSolver Λ ((SummCtx.base Λ).update (.param 0)
      ((Summary.id Λ).specialise 0 (.param 0) [Summary.id Λ])) :=
  .specialise .nil (trySpecialise_id_param Λ)

/-! ### Every summary of a well-formed type space is in anonymous order

The base summaries are; a summary derived from a call produces the result type constructor of
the called function, which a library orders that way (`Library.tyParamsOrdered`); and pinning a
type parameter preserves the order (`TyConsId.InAnonOrder.substCons_specSubst`). -/

/-- Every summary of the base type space names its type parameters in the order of the
constructor it produces. -/
theorem SummCtx.base_inAnonOrder {Λ : Library} {τ : TyConsId} {ς : Summary}
    (hin : (SummCtx.base Λ).MemTy τ ς) : ς.src.fn.ty.InAnonOrder := by
  simp only [SummCtx.base, List.foldr_cons, List.foldr_nil] at hin
  rcases SummCtx.mem_update hin with ⟨-, rfl⟩ | hin
  · exact (by decide : (TyConsId.param 0).InAnonOrder)
  iterate 4
    rcases SummCtx.mem_update hin with ⟨-, rfl⟩ | hin
    · decide
  exact absurd hin List.not_mem_nil

/-- Every summary derived from a call names its type parameters in the order of the
constructor it produces: that constructor is the result type constructor of the called
function, which the library orders that way. -/
theorem Library.tryRefute_inAnonOrder {Λ : Library} {L : Logic.{0}} {Θ : Solver} {S : SummCtx}
    {τ : TyConsId} {ς : Summary} (h : Λ.TryRefute L Θ S τ (.inl ς)) :
    ς.src.fn.ty.InAnonOrder := by
  obtain ⟨f, φ, hmaps, -, -, ςs, -, -, -, -, -, -, -, -, rfl⟩ := h
  show (φ.callSource f ςs).fn.ty.InAnonOrder
  rw [FunDecl.callSource_ty]
  exact Λ.tyParamsOrdered f φ hmaps

/-- **Every summary of a well-formed type space names its type parameters in the order of the
constructor it produces.** -/
theorem WfSummCtx.inAnonOrder {L : Logic.{0}} {Θ : Solver} {Λ : Library} {S : SummCtx}
    (h : WfSummCtx L Θ Λ S) : ∀ τ ς, S.MemTy τ ς → ς.src.fn.ty.InAnonOrder := by
  induction h with
  | nil => exact fun _ _ hin => SummCtx.base_inAnonOrder hin
  | cons _ hrefute ih =>
    intro τ' ς' hin
    rcases SummCtx.mem_update hin with ⟨-, rfl⟩ | hin
    · exact Library.tryRefute_inAnonOrder hrefute
    · exact ih τ' ς' hin
  | specialise _ hspec ih =>
    obtain ⟨ς₀, ⟨C₀, hmem⟩, i, -, τ, ςs, -, -, rfl, rfl, -⟩ := hspec
    intro τ' ς' hin
    rcases SummCtx.mem_update hin with ⟨-, rfl⟩ | hin
    · exact (ih _ _ hmem).substCons_specSubst i τ.anon
    · exact ih τ' ς' hin

/-! ### Inference soundness -/

/-- Soundness of well-formed type summary contexts, inferred in a sound logic. -/
theorem summCtx_soundness {L : Logic.{0}} (hL : L.Sound) {Λ : Library} {S : SummCtx}
    (hsumm : WfSummCtx L semSolver Λ S) : S.Valid Λ := by
  induction hsumm with
  | nil => exact SummCtx.base_valid
  | cons hwf hrefute hctx =>
    obtain ⟨f, φ, hmaps, rfl, hsafe, ςs, hpicks,
      ε, Ψ, hcall, Ψ', hequiv, hsat, ⟨rfl, rfl⟩
    ⟩ := hrefute
    replace hsat := (semSolver_sat_owned_symAsrt (ς := φ.summary f ςs Ψ')).mp hsat
    intro τ' ς' hin
    rcases SummCtx.mem_update hin with ⟨hm, rfl⟩ | hin
    · exact ⟨(source_reachable hL hmaps hsafe hctx hwf.inAnonOrder hpicks hcall hequiv).of_match
          hm.symm,
        hsat, φ.summary_wellShaped f ςs Ψ'
          (fun p hp => (hpicks.valid hctx p.1 p.2 hp).wellShaped)⟩
    · exact hctx τ' ς' hin
  | specialise hwf hspec hctx =>
    obtain ⟨ς, ⟨C₀, hmem⟩, i, hi, τ, ςs, hςs, hlen, rfl, rfl, hsat⟩ := hspec
    have hord : ∀ ς'' ∈ ςs, ς''.src.fn.ty.InAnonOrder :=
      fun ς'' hς'' => hwf.inAnonOrder _ _ (hςs ς'' hς'')
    replace hsat := semSolver_sat_owned_symAsrt.mp hsat
    intro τ' ς' hin
    rcases SummCtx.mem_update hin with ⟨hm, rfl⟩ | hin
    · exact ((Summary.specialise_valid hi (TyConsId.anon_anon τ) (hctx _ _ hmem)
        (fun ς'' hς'' => (hctx _ _ (hςs ς'' hς'')).of_match (TyConsId.match_anon τ)) hord
          (hlen.trans Source.length_specParams.symm)
          hsat).of_match hm.symm)
    · exact hctx τ' ς' hin

/-! ### Auxiliary lemmas -/

private theorem frame_err_preservation {Λ : Library} {e : Expr} {h h' : Heap} {ε : Exit}
    (hstep : Λ ⊢ ⟨h | e⟩ ⇓ᵢ ⟨h' | ε⟩) (herr : ε.toFull = Exit.err):
    ∃ h, Λ ⊢ ⟨∅ | e⟩ ⇓ ⟨h | .err⟩ := by
  obtain ⟨hs', _, hcase⟩ := frame_subtraction hstep ∅ h (by simp) (by simp)
  rcases hcase with ⟨hstep, _⟩ | ⟨l, hstep, _⟩
  · rw [← herr]
    exact ⟨hs', semantics_preservation hstep⟩
  · exact ⟨hs', semantics_preservation hstep⟩

/-! ### Inadequacy result of RUXt -/

/-- **Adequacy result for refuted type assignments**: a refuted type assignment is
inadequate.

The witness is a well-typed main program (`Summary.witness_safeMain`), and it goes wrong since
the model exhibits a state in which the error postcondition holds, reached from the state the
let-bound programs build up (`Summary.witness_frameStep`). -/
theorem inadequacy {Λ : Library} {e : Expr}
    (hrefuted : Λ.HasRefutedType e) : Λ.Inadequate e := by
  obtain ⟨L, hL, Sctx, hwf, τ, f, φ, hmaps, rfl, hsafe, ςs, hpicks,
    εₗ, Ψ, hcall, Ψ', hequiv, hsatOwned, Hnok, P, hP, margs, hmodel, rfl
  ⟩ := hrefuted
  obtain ⟨res, vs, hmodel⟩ := semSolver_model_typedSymAsrt.mp hmodel
  set wargs := margs.ulower
  set args : TeleArg (φ.summary f ςs Ψ').ownedTele := wargs.fst.app vs
  obtain hctx := summCtx_soundness hL hwf
  have hshape := φ.summary_wellShaped f ςs Ψ'
    (fun p hp => (hpicks.valid hctx p.1 p.2 hp).wellShaped)
  obtain ⟨-, htc, hux⟩ := source_reachable hL
    hmaps hsafe hctx hwf.inAnonOrder hpicks hcall hequiv
  set subvs : SubvArgs.{0} (φ.summary f ςs Ψ').src.arity :=
    TypePicks.subvArgs P (φ.summary f ςs Ψ').src.arity wargs.snd
    with hsubvs
  refine ⟨_, Summary.witness_safeMain hctx hP htc wargs, ?semStep⟩
  case semStep =>
    obtain ⟨h', hΦ⟩ := hmodel
    have hpost : HProp h' ((φ.summary f ςs Ψ').post res args subvs) := by
      rw [Summary.post_apply]; exact hΦ
    obtain ⟨vs, hΨ⟩ := (hequiv.ownedAt (f := f) res _ subvs h').mp hΦ
    have hcallux := uxTriple_poly.mp (hcall.uxFrameTriple hL)
    obtain ⟨-, -, ε, ⟨hε, -⟩⟩ := hcallux _ subvs _ _ hΨ
    obtain ⟨hp, hpre, ε', hε', hstep⟩ :=
      Summary.uxFrameTriple_triple_iff.mp hux args subvs res h' hpost
    obtain rfl : ε = ε' := Option.some.inj (hε.symm.trans hε')
    obtain herr : ε.toFull = .err := by
      cases εₗ; contradiction
      · let .unit := res; cases hε; rfl
      · let .loc _ := res; cases hε; rfl
    exact frame_err_preservation (Summary.witness_frameStep hctx hP htc hshape hpre hstep) herr

end RUXt
