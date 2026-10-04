import RUXt.Semantics.Summary.Basic
import RUXt.Semantics.Summary.Source.Specialise

/-!
# Validity of a specialised summary

`Summary.specialise` preserves validity (`Summary.specialise_valid`), given the
satisfiability of the specialised postcondition.

The proof uses the *strengthened* triple `Summary.SpecReachable` of the summary being
specialised, in which the resources required at a pinned parameter are given by the
postcondition of the summary supplied for it (`Source.specPreVals`).  It follows from validity
(`Summary.Valid.specStrong`, `SummCtx.Valid.specStrong`), since the precondition of a summary
(`Summary.pre`) describes each input value through the subvariant of its rank in the typed
subvariant of its type parameter.
-/

namespace RUXt

open scoped PFun

/-- The strengthened triple of a summary at its type parameter `i`: every state satisfying its
postcondition is reached by running its source from the resources
`Source.specPreVals` describes — the resources the typed subvariant supplied for the pinned
type parameter requires of the values the let-bound sources produce, at the rank of the
parameter each of them is bound to, and the resources of the other typed subvariant arguments
at the remaining input values. -/
def Summary.SpecReachable (ς : Summary) (Λ : Library) (i : TyIdx) : Prop :=
  ∀ (S : SubvArgs.{0} ς.src.arity)
    (syms : TeleArg ς.src.teleOf) (rs vs : List Val)
    (r : Val) (h' : Heap),
    HProp h' (ς.ownedAt r
        (syms.app (TeleArg.ofListPad Val.unit ς.valArity
          (weaveVals i vs rs ς.src.fn.params))) S) →
      ∃ h, HProp h (Source.specPreVals Λ i S (fun _ => 0) ς.src.fn.params rs vs)
        ∧ (Λ ⊢ ⟨h | ((ς.src.fn.body.apply syms).apply S.tys).substs ς.src.fn.paramNames
              (Term.ofVals (weaveVals i vs rs ς.src.fn.params))⟩ ⇓ᵢ ⟨h' | .ok r⟩)

/-- A summary satisfies the strengthened triple at every type parameter of its source. -/
def Summary.SpecStrong (ς : Summary) (Λ : Library) : Prop :=
  ∀ i : TyIdx, ς.SpecReachable Λ i

/-- Every summary of a type space satisfies the strengthened triple. -/
def SummCtx.SpecStrong (S : SummCtx) (Λ : Library) : Prop :=
  ∀ C ς, S.MemTy C ς → ς.SpecStrong Λ

/-! ## Properties -/

/-! ### Reading the typed subvariant arguments of a supplied summary -/

/-- The typed subvariant arguments of a summary valid at `τ` are exactly the ones for the type
parameters of `τ` followed by its free ones: the two sizes agree. -/
theorem Summary.Valid.arity_add_freeArity {Λ : Library} {ς : Summary} {τ : TyConsId}
    (h : ς.Valid Λ τ) : τ.arity + ς.src.freeArity = ς.src.arity := by
  rw [← h.src_ty.arity_eq]
  exact TyConsId.arity_add_freeArity h.typechecks.ty_bounded

/-! ### The specialised summary -/

namespace Summary

variable {Λ : Library} {ς : Summary} {i : TyIdx} {τ : TyConsId} {ςs : List Summary}

@[simp] theorem specialise_src :
    (ς.specialise i τ ςs).src
      = Source.specialise (maxNameLen (ς.src.fn.paramNames ++ ςs.flatMap fun ς' => ς'.src.fn.paramNames)) ς.src i τ
          ςs := rfl

/-- The postcondition of a specialised summary, for a type constructor `τ` in anonymous form:
the postcondition of `ς` at the typed subvariant describing the pinned type, and at some list `rs`
of values the let-bound sources produce — the only quantified binder.  The input values `ς` keeps
are the first block of input values, those of the supplied summaries the final one.  The typed
subvariant arguments of `ς` are the blocks of `S` arranged in the order of its type parameters:
the first `i`, the pinned typed subvariant, then the `ς.src.arity - 1 - i` following the
`τ.arity` ones for the type parameters of `τ`. -/
theorem specialise_ownedAt (hτ : τ.anon = τ) (r : Val)
    (args : TeleArg (ς.specialise i τ ςs).ownedTele)
    (S : SubvArgs.{0} (ς.specialise i τ ςs).src.arity) {h : Heap} :
    HProp h ((ς.specialise i τ ςs).ownedAt r args S)
      ↔ ∃ rs : List Val, HProp h (ς.ownedAt r
            (TeleArg.app args.fst.fst
              (TeleArg.ofListPad Val.unit ς.valArity
                (weaveVals i
                  (args.snd.splitUniform (ς.valArity - ςs.length)
                    (Source.mergedValArity (ςs.map Summary.src))).1.toList
                  rs ς.src.fn.params)))
            ((S.block default 0 i).appendUniform
                ((S.block default (i + τ.arity) (ς.src.arity - 1 - i)).consUniform
                  ⟨(τ.shiftTo i).concretise S.tys,
                    SubvArgs.ownAssertions (S.block default i τ.arity) ςs
                      (S.block default (ς.src.arity - 1 + τ.arity)
                        (Source.mergedFreeArity (ςs.map Summary.src)))
                      args.fst.snd
                      (args.snd.splitUniform (ς.valArity - ςs.length)
                        (Source.mergedValArity (ςs.map Summary.src))).2⟩)
              |>.reindex default _root_.id ς.src.arity)) := by
  have hT : ∀ j < τ.arity, SubvArgs.get (S.block default i τ.arity) j = S.get (i + j) :=
    fun j hj => SubvArgs.get_block S i hj
  rw [Summary.ownedAt]
  unfold Summary.specialise
  simp only [Subvariant.specialise_at, Subvariant.specialiseAt,
    TyConsId.instantiate_tys_of_get hτ S _ hT]
  rfl

end Summary

/-! ### Validity of a specialised summary -/

namespace Summary

variable {Λ : Library} {ς : Summary} {i : TyIdx} {τ : TyConsId}
  {C : TyConsId} {ςs : List Summary}

/-- A valid summary satisfies the strengthened triple: at the parameters carrying the pinned
type parameter, its precondition requires exactly the resources the description `o` of the
pinned type gives. -/
theorem Valid.specStrong (h : ς.Valid Λ C) : ς.SpecStrong Λ := by
  intro i S syms rs vs r h' hpost
  have hvals : (weaveVals i vs rs ς.src.fn.params).length = ς.valArity :=
    (length_weaveVals i vs rs ς.src.fn.params).trans h.wellShaped
  obtain ⟨hp, hpprop, -, ⟨⟩, hstep⟩ :=
    h.triple_apply
      (TeleArg.app syms (TeleArg.ofListPad Val.unit ς.valArity
        (weaveVals i vs rs ς.src.fn.params))) S
      r h' (by rw [Summary.post_apply]; exact hpost)
  rw [Summary.pre_apply] at hpprop
  rw [Summary.expr_apply] at hstep
  simp only [TeleArg.fst_append, TeleArg.snd_append,
    TeleArg.toList_ofListPad Val.unit hvals] at hpprop hstep
  rw [show ς.src.fn.paramCons = ς.src.fn.params.map Prod.snd from rfl,
    Source.ownValsAt_weaveVals] at hpprop
  exact ⟨hp, hpprop, hstep⟩

/-- The sources of summaries valid at `τ` satisfy `Source.Ok`. -/
theorem srcs_ok (hςs : ∀ ς' ∈ ςs, ς'.Valid Λ τ) : ∀ s' ∈ ςs.map Summary.src, s'.Ok Λ := by
  intro s' hs'
  obtain ⟨ς', hς', rfl⟩ := List.mem_map.mp hs'
  exact (hςs ς' hς').src_ok

/-- The sources of summaries valid at `τ` produce a constructor matching `τ`. -/
theorem srcs_match (hςs : ∀ ς' ∈ ςs, ς'.Valid Λ τ) :
    ∀ s' ∈ ςs.map Summary.src, s'.fn.ty.Match τ := by
  intro s' hs'
  obtain ⟨ς', hς', rfl⟩ := List.mem_map.mp hs'
  exact (hςs ς' hς').src_ty

/-- The input values of a specialised summary: the ones the summary being specialised keeps,
followed by those of the sources let-bound for the supplied summaries. -/
theorem specialise_valArity (ς : Summary) (i : TyIdx)
    (τ : TyConsId) (ςs : List Summary) :
    (ς.specialise i τ ςs).valArity
      = ς.valArity - ςs.length + Source.mergedValArity (ςs.map Summary.src) := rfl

/-- Specialising a well-shaped summary gives a well-shaped summary: the specialised source has
one parameter per input value the summary keeps, followed by one per input value of a supplied
source. -/
theorem specialise_wellShaped (ς : Summary) (i : TyIdx)
    (τ : TyConsId) (ςs : List Summary) (hς : ς.WellShaped)
    (hlen : ςs.length = (ς.src.specParams i).length) :
    (ς.specialise i τ ςs).WellShaped := by
  show (Source.specialise (maxNameLen (ς.src.fn.paramNames ++ ςs.flatMap fun ς' => ς'.src.fn.paramNames)) ς.src i τ
    ςs).fn.params.length = _
  rw [Source.specialise_params (fun _ => Expr.val Val.unit) ((List.length_map _).trans hlen),
    List.length_append,
    List.length_map, Expr.bindSourcesAux_params_length, specialise_valArity]
  have hsplit := Source.length_restParams_add_specParams ς.src i
  have hw : ς.src.fn.params.length = ς.valArity := hς
  omega

/-- The supplied summaries run their sources one after the other on the input values the
specialised source hands to them: the resources their postconditions describe, at the values
`rs` their sources are claimed to produce — one per summary — are exactly the ones
produced by running those sources to those very values.

The shared block `T` is the block at `A` in the tuple `S` with the subvariants of the parameters
of the summaries already visited removed (`Source.dropSubvArgs`), as many at each component as the
offsets `off`; the free typed subvariants left in `F` sit at `B + D`, after the `D` free ones of
the summaries already visited. -/
theorem runs_of_ownAssertions {M : ℕ} (S : SubvArgs.{0} M) (A B : ℕ) (hAB : A + τ.arity ≤ B) :
    ∀ (ςs : List Summary) (L D : ℕ) (T : SubvArgs.{0} τ.arity)
      (F : SubvArgs.{0} (Source.mergedFreeArity (ςs.map Summary.src)))
      (off : TyConsId → ℕ)
      (syms : TeleArg (Source.mergedTeleOf (ςs.map Summary.src)))
      (bs : TeleArg (Tele.uniform Val (Source.mergedValArity (ςs.map Summary.src))))
      (rs : List Val) (h : Heap),
      (∀ j < τ.arity, T.get j
        = ⟨(S.get (A + j)).ty, (S.get (A + j)).own.drop (off (.param (A + j)))⟩) →
      (∀ j, F.get j = S.get (B + D + j)) →
      (∀ j, off (.param (B + D + j)) = 0) →
      (∀ ς' ∈ ςs, ς'.Valid Λ τ) → (∀ ς' ∈ ςs, ς'.src.fn.ty.InAnonOrder) →
      ςs.length ≤ L → rs.length = ςs.length →
      HProp h (Asrt.iter (rs.zip (SubvArgs.ownAssertions T ςs F syms bs))
        fun p => p.2 p.1) →
      ∃ g, Source.Runs Λ (fun C => C.ownsAt Λ S) S.tys (ςs.map Summary.src) off
        (List.replicate L ((List.range τ.arity).map (A + ·))) (B + D) syms bs rs g h := by
  intro ςs
  induction ςs with
  | nil =>
    intro L D T F off syms bs rs h _ _ _ _ _ _ hrs hprop
    obtain rfl : rs = [] := List.length_eq_zero_iff.mp hrs
    obtain rfl : h = ∅ := hprop
    exact ⟨∅, Source.runs_nil.mpr ⟨rfl, rfl, rfl⟩⟩
  | cons ς₀ ςs ih =>
    intro L D T F off syms bs rs h hT hF hoff hvalid hord hL hrs hprop
    obtain _ | ⟨r₀, rs⟩ := rs; · simp at hrs
    have hς₀ : ς₀.Valid Λ τ := hvalid ς₀ List.mem_cons_self
    have hord₀ : ς₀.src.fn.ty.InAnonOrder := hord ς₀ List.mem_cons_self
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by simp at hL; omega⟩
    have hN : ς₀.src.fn.ty.arity = τ.arity := hς₀.src_ty.arity_eq
    have hn : τ.arity + ς₀.src.freeArity = ς₀.src.arity := hς₀.arity_add_freeArity
    have hparam : ∀ C ∈ ς₀.src.fn.paramCons, ∃ k < ς₀.src.arity, C = .param k :=
      List.forall_mem_map.mpr hς₀.typechecks.src_valid.1
    -- The embedding of the type parameters of the head summary: a shift of each block.
    set ρ := ς₀.src.ren ((List.range τ.arity).map (A + ·)) (B + D) with hρdef
    have hρ : ∀ j < ς₀.src.arity,
        ρ j = if j < τ.arity then A + j else B + D + (j - τ.arity) :=
      fun j hj => Source.ren_of_inAnonOrder ς₀.src hord₀ hN A _ hj
    have hinj : ∀ j < ς₀.src.arity, ∀ j' < ς₀.src.arity, ρ j = ρ j' → j = j' := by
      intro j hj j' hj' hjj
      rw [hρ j hj, hρ j' hj'] at hjj
      have hjj' : @Eq ℕ (if j < τ.arity then (A + j : ℕ) else (B + D + (j - τ.arity) : ℕ))
          (if j' < τ.arity then (A + j' : ℕ) else (B + D + (j' - τ.arity) : ℕ)) := hjj
      split_ifs at hjj' <;> omega
    set Fs := TeleArg.splitUniform ς₀.src.freeArity
      (Source.mergedFreeArity (ςs.map Summary.src)) F with hFs
    -- The typed subvariant arguments the head summary is read at.
    set P : SubvArgs.{0} ς₀.src.arity :=
      (T.appendUniform Fs.1).reindex default _root_.id ς₀.src.arity with hPdef
    have hPget : ∀ j, P.get j
        = SubvArgs.get (T.appendUniform Fs.1 :
            SubvArgs.{0} (τ.arity + ς₀.src.freeArity)) j := by
      intro j
      rw [hPdef, SubvArgs.get, SubvArgs.get, TeleArg.toList_reindex_id _ _ hn]
    have hPfree : ∀ j, τ.arity ≤ j → j < ς₀.src.arity →
        P.get j = S.get (B + D + (j - τ.arity)) := by
      intro j hj hj'
      obtain ⟨k, rfl⟩ : ∃ k, j = τ.arity + k := ⟨j - τ.arity, by omega⟩
      rw [hPget, SubvArgs.get_appendUniform_right, hFs,
        SubvArgs.get_splitUniform_left _ (by omega), hF, Nat.add_sub_cancel_left]
    have hPshared : ∀ j < τ.arity, P.get j
        = ⟨(S.get (A + j)).ty, (S.get (A + j)).own.drop (off (.param (A + j)))⟩ := by
      intro j hj
      rw [hPget, SubvArgs.get_appendUniform_left _ _ hj, hT j hj]
    -- The parameters of the head summary are ranked in the merge from the offsets `off`, and
    -- read, at the tuple `P`, the very subvariants they are ranked at.
    have hcoh : ∀ i, TyConsId.param i ∈ ς₀.src.fn.paramCons → ∀ k g,
        (TyConsId.selRanks ρ off ς₀.src.fn.paramCons i)[k]? = some g →
        ∀ v, (P.get i).get Λ ((fun _ => 0 : TyConsId → ℕ) (.param i) + k) v
          = (S.get (ρ i)).get Λ g v := by
      intro i hi k g hg v
      obtain ⟨_, hi', ⟨⟩⟩ := hparam _ hi
      rw [TyConsId.selRanks_eq_map_range hinj _ off i hi' hparam] at hg
      obtain ⟨hk, hgk⟩ := List.getElem?_eq_some_iff.mp hg
      rw [List.getElem_map, List.getElem_range] at hgk
      subst hgk
      rw [Nat.zero_add, hρ i hi']
      by_cases hiN : i < τ.arity
      · rw [if_pos hiN, hPshared i hiN]
        simp only [TypedSubvariants.get, List.getElem?_drop]
      · rw [if_neg hiN, hPfree i (Nat.le_of_not_lt hiN) hi', hoff, Nat.zero_add]
    have hpre_eq : ∀ vs : List Val,
        FunTempl.ownValsAt (fun C => C.ownsAt Λ S) off
            (ς₀.src.renCons ((List.range τ.arity).map (A + ·)) (B + D)) vs
          = FunTempl.ownValsAt (fun C => C.ownsAt Λ P) (fun _ => 0) ς₀.src.fn.paramCons vs :=
      fun vs => FunTempl.ownValsAt_select S P ρ _ vs off (fun _ => 0)
        (fun C hC => (hparam C hC).imp fun _ h => h.2) hcoh
    -- The types of `P` are the type arguments the source construction runs the head source at.
    have htys : P.tys
        = ς₀.src.tyArgs ((List.range τ.arity).map (A + ·)) (B + D) S.tys := by
      refine TeleArg.toList_injective _ _ ?_
      rw [SubvArgs.toList_tys, Source.tyArgs, TyArgs.toList_reindex]
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      have hi : i < ς₀.src.arity := by simpa using h2
      have hget : (TeleArg.toList P)[i]'(by simpa using h1) = P.get i := by
        rw [SubvArgs.get, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]
      rw [List.getElem_map, List.getElem_map, List.getElem_range, hget, SubvArgs.get_tys,
        Source.ren_of_inAnonOrder ς₀.src hord₀ hN A _ hi]
      split_ifs with hiN
      · rw [hPshared i hiN]
      · rw [hPfree i (Nat.le_of_not_lt hiN) hi]
    -- Split the resources of the head summary from those of the remaining ones.
    rw [SubvArgs.ownAssertions_cons, List.zip_cons_cons] at hprop
    obtain ⟨h₁, h₂, rfl, hdisj12, hhead, htail⟩ := hprop
    rw [← hFs] at hhead htail
    set vs := (TeleArg.splitUniform ς₀.src.fn.params.length
        (Source.mergedValArity (ςs.map Summary.src)) bs).1 with hvs
    obtain ⟨g₁, hpre₁, -, ⟨⟩, hstep₁⟩ :=
      hς₀.triple_apply
        (TeleArg.app syms.fst (vs.reindex Val.unit _root_.id ς₀.valArity)) P r₀ h₁
        (by rw [Summary.post_apply]; exact hhead)
    rw [Summary.pre_apply] at hpre₁
    rw [Summary.expr_apply] at hstep₁
    have hw : ς₀.src.fn.params.length = ς₀.valArity := hς₀.wellShaped
    simp only [TeleArg.fst_append, TeleArg.snd_append,
      TeleArg.toList_reindex_id Val.unit vs hw] at hpre₁ hstep₁
    rw [← hpre_eq] at hpre₁
    rw [htys] at hstep₁
    -- The remaining summaries read the shared typed subvariants with those of the parameters of
    -- the head summary removed, and the remaining free ones.
    have hoffA : ∀ j < τ.arity, TyConsId.offAfter off
        (ς₀.src.renCons ((List.range τ.arity).map (A + ·)) (B + D)) (.param (A + j))
          = off (.param (A + j)) + ς₀.src.paramCount j := by
      intro j hj
      rw [TyConsId.offAfter, Source.paramCount,
        show ς₀.src.renCons ((List.range τ.arity).map (A + ·)) (B + D)
          = ς₀.src.fn.paramCons.map (·.rename ρ) from rfl,
        TyConsId.count_map_rename_param (x := A + j) (j := j) _ hparam fun k hk => by
          rw [hρ k hk]
          split_ifs <;> constructor <;> intro <;> omega]
    have hT' : ∀ j < τ.arity, (ς₀.src.dropSubvArgs T (List.range τ.arity)).get j
        = ⟨(S.get (A + j)).ty, (S.get (A + j)).own.drop (TyConsId.offAfter off
            (ς₀.src.renCons ((List.range τ.arity).map (A + ·)) (B + D)) (.param (A + j)))⟩ := by
      intro j hj
      rw [Source.get_dropSubvArgs_range _ _ hj, hT j hj, hoffA j hj, List.drop_drop]
    have hF' : ∀ j, SubvArgs.get Fs.2 j = S.get (B + (D + ς₀.src.freeArity) + j) := by
      intro j
      rw [hFs, SubvArgs.get_splitUniform_right, hF]
      congr 1
      omega
    have hoff' : ∀ j, TyConsId.offAfter off
        (ς₀.src.renCons ((List.range τ.arity).map (A + ·)) (B + D))
        (.param (B + (D + ς₀.src.freeArity) + j)) = 0 := by
      intro j
      rw [TyConsId.offAfter,
        show B + (D + ς₀.src.freeArity) + j
          = B + D + (ς₀.src.freeArity + j) by omega, hoff, Nat.zero_add]
      exact TyConsId.count_map_rename_param_eq_zero _ hparam fun k hk => by
        rw [Source.ren_of_inAnonOrder ς₀.src hord₀ hN A _ hk]
        split_ifs <;> omega
    obtain ⟨g₂, hruns₂⟩ :=
      ih L (D + ς₀.src.freeArity) (ς₀.src.dropSubvArgs T (List.range τ.arity)) Fs.2
        (TyConsId.offAfter off
          (ς₀.src.renCons ((List.range τ.arity).map (A + ·)) (B + D)))
        syms.snd
        (TeleArg.splitUniform ς₀.src.fn.params.length
          (Source.mergedValArity (ςs.map Summary.src)) bs).2
        rs h₂ hT' hF' hoff'
        (fun ς' hς' => hvalid ς' (List.mem_cons_of_mem _ hς'))
        (fun ς' hς' => hord ς' (List.mem_cons_of_mem _ hς'))
        (by simpa using hL) (by simpa using hrs) htail
    rw [← Nat.add_assoc] at hruns₂
    refine ⟨g₁ ∪ g₂, Source.runs_cons.mpr
      ⟨r₀, _, g₁, g₂, h₁, h₂, rfl, rfl, rfl, hdisj12,
        ?_, ?_, ?_⟩⟩
    · simpa only [List.replicate_succ, List.headD_cons] using hpre₁
    · simpa only [List.replicate_succ, List.headD_cons] using hstep₁
    · simpa only [List.replicate_succ, List.headD_cons, List.tail_cons] using hruns₂
/-- The type constructors of the parameters of a specialised summary: the ones the kept
parameters carry, specialised, followed by those of the merged supplied sources. -/
theorem specialise_src_paramCons (hlen : ςs.length = (ς.src.specParams i).length) :
    (ς.specialise i τ ςs).src.fn.paramCons
      = (ς.src.restParams i).map (fun p => p.2.substCons (TyConsId.specSubst i τ))
        ++ (bindSourcesAux (N := ς.src.arity - 1 + τ.arity
              + Source.mergedFreeArity (ςs.map Summary.src))
            (fun _ => Expr.val Val.unit)
            (PVar.freshen (maxNameLen (ς.src.fn.paramNames ++ ςs.flatMap fun ς' => ς'.src.fn.paramNames)))
            (ς.src.specVars i)
            (ς.src.fn.ty.substCons (TyConsId.specSubst i τ)) (ς.src.arity - 1 + τ.arity)
            (ς.src.specSels i τ) (ςs.map Summary.src)).paramCons := by
  show (ς.specialise i τ ςs).src.fn.params.map Prod.snd = _
  rw [specialise_src, Source.specialise_params (fun _ => Expr.val Val.unit)
    ((List.length_map _).trans hlen), List.map_append, List.map_map]
  rfl

/-- The state `[lok : owned]` is reachable from the source of a specialised summary: the
supplied sources are run first, on the resources their own input values require, and produce
exactly the resources the triple of the summary being specialised requires at the parameters
they are let-bound to. -/
theorem specialise_reachable (hi : i < ς.src.arity) (hτ : τ.anon = τ)
    (hς : ς.Valid Λ C) (hςs : ∀ ς' ∈ ςs, ς'.Valid Λ τ)
    (hord : ∀ ς' ∈ ςs, ς'.src.fn.ty.InAnonOrder)
    (hlen : ςs.length = (ς.src.specParams i).length) :
    (ς.specialise i τ ςs).Reachable Λ
      (ς.src.fn.ty.substCons (TyConsId.specSubst i τ)) .lok := by
  -- The parameters of the supplied sources are freshened away from every name in sight.
  have hsrclen : ∀ ς' ∈ ςs, ∀ y ∈ ς'.src.fn.paramNames,
      y.length ≤ maxNameLen (ς.src.fn.paramNames ++ ςs.flatMap fun ς' => ς'.src.fn.paramNames) :=
    fun ς' hς' _ hy =>
      le_maxNameLen (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ς', hς', hy⟩))
  have hvarlen : ∀ y ∈ ς.src.fn.paramNames,
      y.length ≤ maxNameLen (ς.src.fn.paramNames ++ ςs.flatMap fun ς' => ς'.src.fn.paramNames) :=
    fun _ hy => le_maxNameLen (List.mem_append_left _ hy)
  have hdup : ς.src.fn.paramNames.Nodup := hς.src_ok.paramNames_nodup
  have hok := srcs_ok hςs
  have hmatch := srcs_match hςs
  have hord' : ∀ s' ∈ ςs.map Summary.src, s'.fn.ty.InAnonOrder := List.forall_mem_map.mpr hord
  have hsrclen' : ∀ s' ∈ ςs.map Summary.src, ∀ y ∈ s'.fn.paramNames,
      y.length ≤ maxNameLen (ς.src.fn.paramNames ++ ςs.flatMap fun ς' => ς'.src.fn.paramNames) :=
    List.forall_mem_map.mpr hsrclen
  have hlen' : (ςs.map Summary.src).length = (ς.src.specParams i).length :=
    (List.length_map _).trans hlen
  have hsel := Source.selsOk_specSels (s := ς.src) (i := i) hi hlen' hmatch
  -- Every parameter of every source involved carries a bare type parameter.
  have hbsrc : ∀ s ∈ ςs.map Summary.src, ∀ p ∈ s.fn.params,
      ∃ j < s.arity, p.2 = TyConsId.param j :=
    List.forall_mem_map.mpr fun ς' hς' => (hςs ς' hς').typechecks.src_valid.1
  refine ⟨TyConsId.Match.refl _,
    Source.specialise_typechecks hς.typechecks hi hτ hok hmatch hord' hvarlen hsrclen' hdup hlen', ?_⟩
  refine uxFrameTriple_triple_iff.mpr fun args S r h' hpost => ?_
  rw [Summary.post_apply, Summary.specialise_ownedAt hτ] at hpost
  -- The values the let-bound sources produce: the ones the postcondition quantifies.
  obtain ⟨rs₀, hpost⟩ := hpost
  -- Only the first `ςs.length` of them are read: take exactly those.
  set rs : List Val := (List.range ςs.length).map (rs₀.getD · .unit) with hrsdef
  have hrsl : rs.length = ςs.length := by simp [hrsdef]
  rw [weaveVals_congr_rs i ς.src.fn.params _ rs₀ rs (fun k hk => by
    have hk' : k < ςs.length := by rw [hlen]; exact hk
    simp [hrsdef, List.getD_eq_getElem?_getD, hk'])] at hpost
  -- The input values of the specialised summary: the ones the summary being specialised keeps
  -- first, then those of the supplied summaries.
  set K : ℕ := ς.valArity - ςs.length with hK
  have hKrest : K = (ς.src.restParams i).length := by
    have hsplit := Source.length_restParams_add_specParams ς.src i
    have hw : ς.src.fn.params.length = ς.valArity := hς.wellShaped
    omega
  set vs : List Val := (args.snd.splitUniform K
    (Source.mergedValArity (ςs.map Summary.src))).1.toList with hvs
  set bs' : TeleArg (Tele.uniform Val (Source.mergedValArity (ςs.map Summary.src))) :=
    (args.snd.splitUniform K (Source.mergedValArity (ςs.map Summary.src))).2 with hbs'def
  have hargs : args.snd.toList = vs ++ bs'.toList :=
    (splitUniform_toList K _ args.snd).symm
  -- The subvariants describing the pinned type: the postcondition of each supplied summary,
  -- in the order of the parameters they are let-bound at.
  -- The typed subvariant arguments, cut into four blocks: the `i` ones `ς` keeps before the
  -- pinned type parameter, the ones for the type parameters of `τ`, the ones `ς` keeps after the
  -- pinned type parameter and the free ones of the supplied sources.
  set τSubvs : SubvArgs.{0} τ.arity := S.block default i τ.arity with hτSubvs
  set freeSubvs : SubvArgs.{0} (Source.mergedFreeArity (ςs.map Summary.src)) :=
    S.block default (ς.src.arity - 1 + τ.arity) (Source.mergedFreeArity (ςs.map Summary.src))
    with hfreeSubvs
  set keptSubvs : SubvArgs.{0} (ς.src.arity - 1) :=
    TeleArg.reindex default (TyConsId.keptIdx i τ.arity) (ς.src.arity - 1) S with hkeptSubvs
  have hkept : ∀ k < ς.src.arity - 1, keptSubvs.get k = S.get (TyConsId.keptIdx i τ.arity k) :=
    fun k hk => SubvArgs.get_reindex hk
  have hτS : ∀ j < τ.arity, τSubvs.get j = S.get (i + j) := fun j hj => SubvArgs.get_block S i hj
  have hfree : ∀ j, freeSubvs.get j = S.get (ς.src.arity - 1 + τ.arity + 0 + j) := fun j => by
    rw [Nat.add_zero]
    by_cases hj : j < Source.mergedFreeArity (ςs.map Summary.src)
    · exact SubvArgs.get_block S _ hj
    · have hSlen : (ς.specialise i τ ςs).src.arity
          = ς.src.arity - 1 + τ.arity + Source.mergedFreeArity (ςs.map Summary.src) := rfl
      rw [SubvArgs.get, SubvArgs.get, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [TeleArg.toList_length]; omega),
        List.getElem?_eq_none (by rw [TeleArg.toList_length]; omega)]
  set os : List (Val → Asrt.{0}) :=
    SubvArgs.ownAssertions τSubvs ςs freeSubvs args.fst.snd bs' with hosdef
  set Sin : SubvArgs.{0} ς.src.arity :=
    TeleArg.insertUniformPred ⟨(τ.shiftTo i).concretise S.tys, os⟩ i keptSubvs
    with hSin
  -- The blocks arranged in the order of the type parameters of `ς` are `Sin`.
  rw [SubvArgs.arrange_eq_insertUniformPred S _ τ.arity hi] at hpost
  -- The typed subvariant the summary is run at, at the pinned position, is the one the
  -- specialisation supplies there.
  have hgetS : SubvArgs.get Sin i = ⟨(τ.shiftTo i).concretise S.tys, os⟩ := by
    rw [hSin, SubvArgs.get, TeleArg.getD_toList_insertUniformPred _ _ i hi _ i, if_pos rfl]
  obtain ⟨hp, hpprop, hpstep⟩ :=
    hς.specStrong i Sin args.fst.fst rs vs r h' hpost
  -- The type arguments the summary being specialised is run at.
  have htys : SubvArgs.tys Sin = ς.src.specTyArgs i τ (SubvArgs.tys S) := by
    rw [hSin, SubvArgs.tys_insertUniformPred_of_get _ S keptSubvs (TyConsId.keptIdx i τ.arity) hkept,
      Source.specTyArgs_eq hτ hi]
  rw [htys] at hpstep
  -- The lengths of the value lists involved.
  have hrslen : rs.length
      = (ς.src.fn.params.filter fun p => p.2 == TyConsId.param i).length := by
    rw [hrsl, hlen]
    rfl
  have hvslen : vs.length
      = (ς.src.fn.params.filter fun p => p.2 != TyConsId.param i).length := by
    rw [hvs, TeleArg.toList_length, hKrest]
    rfl
  have hoslen : os.length = rs.length := by
    rw [hosdef, SubvArgs.length_ownAssertions, hrslen]
    exact hlen
  -- The pinned parameter of rank `k` is described by the `k`-th supplied summary.
  have hread : ∀ (k : ℕ) (hk : k < os.length) (v : Val),
      (SubvArgs.get Sin i).get Λ (0 + k) v = os[k] v := by
    intro k hk v
    rw [Nat.zero_add, hgetS]
    exact TypedSubvariants.get_of_getElem? (List.getElem?_eq_getElem hk) v
  -- Split the resources into the ones the let-bound sources produce and the ones kept.
  obtain ⟨hP, hF, rfl, hdisjPF, hpin, hrest⟩ :=
    Source.hProp_specPreVals_split Sin ς.src.fn.params os rs vs (fun _ => 0) hp
      hrslen hvslen hoslen hread hpprop
  -- Run the supplied sources.
  obtain ⟨g, hruns⟩ :=
    runs_of_ownAssertions S i (ς.src.arity - 1 + τ.arity)
      (Nat.add_le_add_right (Nat.le_sub_one_of_lt hi) _)
      ςs (ς.src.specParams i).length 0 τSubvs freeSubvs
      (fun _ => 0) args.fst.snd bs' rs hP
      (fun j hj => by rw [hτS j hj, List.drop_zero]) hfree
      (fun _ => rfl) hςs hord
      (le_of_eq hlen)
      hrsl hpin
  rw [Nat.add_zero] at hruns
  rw [← TyConsId.params_shiftTo] at hruns
  rw [PFun.union_comm hdisjPF] at hpstep
  obtain ⟨hpre, hdisjg, hchain⟩ :=
    Source.specialise_frameStep (Λ := Λ) hi hς.src_ok hok hmatch hord' hsel hsrclen' hvarlen hdup
      hlen' args.fst.fst args.fst.snd (SubvArgs.tys S) bs' vs rs g hF hP h' (Exit.ok r)
      hvslen hdisjPF.symm hruns hpstep
  -- The type constructors the parameters of the merged supplied sources carry.
  set bcons : List TyConsId :=
    (bindSourcesAux (N := ς.src.arity - 1 + τ.arity
          + Source.mergedFreeArity (ςs.map Summary.src))
        (fun _ => Expr.val Val.unit)
            (PVar.freshen (maxNameLen (ς.src.fn.paramNames ++ ςs.flatMap fun ς' => ς'.src.fn.paramNames)))
            (ς.src.specVars i)
        (ς.src.fn.ty.substCons (TyConsId.specSubst i τ)) (ς.src.arity - 1 + τ.arity)
        (ς.src.specSels i τ) (ςs.map Summary.src)).paramCons with hbcons
  set kcons : List TyConsId :=
    (ς.src.restParams i).map fun p => p.2.substCons (TyConsId.specSubst i τ) with hkcons
  have hkconslen : vs.length = kcons.length := by
    rw [hkcons, List.length_map, hvs, TeleArg.toList_length, hKrest]
  -- The kept parameters carry a type parameter of the source other than the pinned one.
  have hCmem : ∀ C' ∈ (ς.src.restParams i).map Prod.snd,
      ∃ j < ς.src.arity, j ≠ i ∧ C' = TyConsId.param j := by
    intro C' hC'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC'
    rw [Source.restParams, List.mem_filter] at hp
    obtain ⟨j, hj, hp2⟩ := hς.src_ok.src_valid.1 p hp.1
    exact ⟨j, hj, fun hji => by simp [hp2, hji] at hp, hp2⟩
  refine ⟨hF ∪ g, ?_, Exit.ok r, rfl, ?_⟩
  · rw [Summary.pre_apply, hargs, specialise_src_paramCons hlen, ← hbcons, ← hkcons,
      FunTempl.ownValsAt_append _ _ _ _ _ _ hkconslen]
    refine (hProp_iter_append _ _ _ _).mpr ⟨hF, g, rfl, hdisjg, ?_, ?_⟩
    · show HProp hF (FunTempl.ownValsAt (fun C' => C'.ownsAt Λ S) (fun _ => 0) kcons vs)
      have hmapeq : kcons
          = ((ς.src.restParams i).map Prod.snd).map (·.substCons (TyConsId.specSubst i τ)) := by
        rw [hkcons, List.map_map]; rfl
      -- Pinning a type parameter is injective on the others.
      have hkey : ∀ a b : ℕ, a ≠ i → b ≠ i →
          (if a < i then a else a - 1) = (if b < i then b else b - 1) → a = b := by
        intro a b ha hb hab
        split at hab <;> split at hab <;> omega
      have hinjr : ∀ C' ∈ (ς.src.restParams i).map Prod.snd,
          ∀ D ∈ (ς.src.restParams i).map Prod.snd,
          C'.substCons (TyConsId.specSubst i τ) = D.substCons (TyConsId.specSubst i τ) → C' = D := by
        intro C' hC' D hD he
        obtain ⟨j, hj, hjne, rfl⟩ := hCmem C' hC'
        obtain ⟨j', hj', hj'ne, rfl⟩ := hCmem D hD
        rw [TyConsId.substCons_param, TyConsId.substCons_param,
          TyConsId.specSubst, TyConsId.specSubst, if_neg hjne, if_neg hj'ne] at he
        rw [hkey j j' hjne hj'ne (TyConsId.keptIdx_inj (by simpa using he))]
      -- The resources a kept parameter requires are the ones its type parameter describes.
      have hownr : ∀ C' ∈ (ς.src.restParams i).map Prod.snd, ∀ k v,
          (C'.substCons (TyConsId.specSubst i τ)).ownsAt Λ S k v = C'.ownsAt Λ Sin k v := by
        intro C' hC' k v
        obtain ⟨j, hj, hjne, rfl⟩ := hCmem C' hC'
        rw [hSin]
        exact TyConsId.ownsAt_param_substCons_specSubst Λ hi hj hjne τ _ S keptSubvs hkept k v
      rw [hmapeq, FunTempl.ownValsAt_map_of_inj (own' := fun C' => C'.ownsAt Λ Sin)
        (fun C' => C'.substCons (TyConsId.specSubst i τ)) ((ς.src.restParams i).map Prod.snd)
        vs (fun _ => 0) (fun _ => 0) hinjr (fun _ _ => rfl) hownr]
      exact hrest
    · -- The parameters of the merged sources are ranked as if the kept ones were not there:
      -- they carry type parameters the kept ones never carry.
      show HProp g (FunTempl.ownValsAt (fun C' => C'.ownsAt Λ S)
        (TyConsId.offAfter (fun _ => 0) kcons) bcons bs'.toList)
      have hoffb : ∀ C' ∈ bcons, TyConsId.offAfter (fun _ => 0) kcons C' = 0 := by
        intro C' hC'
        obtain ⟨k, hk, hkeq⟩ :=
          Expr.mem_bindSourcesAux_paramCons_of
            (fun k => (i ≤ k ∧ k < i + τ.arity) ∨ ς.src.arity - 1 + τ.arity ≤ k)
            (ςs.map Summary.src)
            (ς.src.specVars i) (ς.src.arity - 1 + τ.arity) (ς.src.specSels i τ)
            (fun _ hk => Or.inr hk)
            (fun o ho j hj => by
              rw [List.eq_of_mem_replicate (show o ∈ List.replicate _ _ from ho)] at hj
              exact Or.inl (TyConsId.mem_params_shiftTo.mp hj))
            hsel hbsrc _ (by rw [← hbcons]; exact hC')
        have hcount : kcons.count C' = 0 := by
          refine List.count_eq_zero_of_not_mem fun hmem => ?_
          obtain ⟨p, hp, hDeq⟩ := List.mem_map.mp hmem
          obtain ⟨j, hj, hjne, hpj⟩ := hCmem p.2 (List.mem_map_of_mem hp)
          rw [hpj] at hDeq
          rw [TyConsId.substCons_param, TyConsId.specSubst, if_neg hjne,
            hkeq] at hDeq
          have hkeylt : ∀ a b c : ℕ, a < c → b < c → b ≠ a →
              (if b < a then b else b - 1) < c - 1 := by
            intro a b c h1 h2 h3
            split <;> omega
          have hlt := TyConsId.keptIdx_lt (i := i) (k := τ.arity)
            (hkeylt i j ς.src.arity hi hj hjne)
          have hjk : TyConsId.keptIdx i τ.arity (if j < i then j else j - 1) = k := by
            simpa using hDeq
          rw [hjk] at hlt
          rcases hk with hk | hk
          · exact TyConsId.keptIdx_notMem_pinned (hjk ▸ hk)
          · omega
        simp [TyConsId.offAfter, hcount]
      rw [FunTempl.ownValsAt_congr_off _ bcons bs'.toList hoffb]
      exact hpre
  · rw [Summary.expr_apply, hargs]
    simpa only [TeleArg.app_fst_snd] using hchain

/-- **Specialisation preserves validity**: the specialised summary is a valid inhabitant of
the specialised type constructor, given the satisfiability of its postcondition, for a pinned
type constructor `τ` in anonymous form. -/
theorem specialise_valid (hi : i < ς.src.arity) (hτ : τ.anon = τ) (hς : ς.Valid Λ C)
    (hςs : ∀ ς' ∈ ςs, ς'.Valid Λ τ) (hord : ∀ ς' ∈ ςs, ς'.src.fn.ty.InAnonOrder)
    (hlen : ςs.length = (ς.src.specParams i).length)
    (hsat : (ς.specialise i τ ςs).SatOwned) :
    (ς.specialise i τ ςs).Valid Λ
      (ς.src.fn.ty.substCons (TyConsId.specSubst i τ)) :=
  ⟨specialise_reachable hi hτ hς hςs hord hlen, hsat,
    specialise_wellShaped ς i τ ςs hς.wellShaped hlen⟩

end Summary

/-! ### The strengthened triple of a valid type space -/

/-- Every summary of a valid type space satisfies the strengthened triple. -/
theorem SummCtx.Valid.specStrong {Λ : Library} {S : SummCtx} (h : SummCtx.Valid Λ S) :
    S.SpecStrong Λ :=
  fun C ς hin => (h C ς hin).specStrong

end RUXt
