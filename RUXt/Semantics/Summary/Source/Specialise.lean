import RUXt.Semantics.Summary.Source.Basic
import RUXt.Semantics.Summary.Subvariant.Specialise

/-!
# The specialisation of a source

The pieces of `Source.specialise`: weaving the input values (`weaveVals`), the split of the
parameters into pinned and kept ones (`Source.pinnedParams`), and the parameters and body of the
specialised source as those of `bindSourcesAux` (`Source.boundParams_eq`,
`Source.bindSources_eq`).  A source in anonymous order (`TyConsId.InAnonOrder`) read at blocks of
type arguments is read along its embedding `Source.ren` (`Source.ren_of_inAnonOrder_sel`,
`Source.tyArgs_blocks`).

Correctness of `Source.specialise`, by reduction to `bindSourcesAux_spec` and
`bindSourcesAux_frameStep`:

* the specialised source is structurally valid and typechecks
  (`Source.specialise_valid`, `Source.specialise_typechecks`);
* its body, run on the resources its parameters require, reproduces the behaviour of the
  body of the source it specialises on the values the let-bound sources produce
  (`Source.specialise_frameStep`).

Also the resources required of the input values of a specialised source
(`Source.specPreVals`), split into the pinned and the kept ones
(`Source.ownValsAt_weaveVals`, `Source.hProp_specPreVals_split`).
-/

namespace RUXt

open scoped PFun

/-! ## Reading a source in anonymous order -/

/-- The type parameters among the first `n` that `range N` does not contain are
`N, …, n - 1`. -/
theorem List.filter_notMem_range {n N : ℕ} (h : N ≤ n) :
    (List.range n).filter (fun x => decide (x ∉ List.range N))
      = (List.range (n - N)).map (N + ·) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [List.range_add, List.filter_append, List.filter_map, Function.comp_def]

/-- The free type parameters of a constructor in anonymous order are the ones following those
it uses. -/
theorem TyConsId.freeIdxs_of_inAnonOrder {c : TyConsId} (hc : c.InAnonOrder) {n : ℕ}
    (hn : c.arity ≤ n) : c.freeIdxs n = (List.range (n - c.arity)).map (c.arity + ·) := by
  rw [TyConsId.freeIdxs, hc]
  exact List.filter_notMem_range hn

/-- The embedding of the type parameters of a source producing a constructor in anonymous order,
bound at the type parameters `osel` with its free type parameters from `B` on: the `N` type
parameters the constructor uses are read off `osel`, position by position, and the free ones
are shifted to start at `B`. -/
theorem Source.ren_of_inAnonOrder_sel (s : Source) (hord : s.fn.ty.InAnonOrder) {N : ℕ}
    (hN : s.fn.ty.arity = N) (osel : List TyIdx) (B : ℕ) {j : ℕ} (hj : j < s.arity) :
    s.ren osel B j = if j < N then osel.getD j 0 else B + (j - N) := by
  unfold Source.ren TyConsId.mergeRen
  have hmem : j ∈ s.fn.ty.params ↔ j < N := by rw [hord, List.mem_range, hN]
  by_cases hjN : j < N
  · rw [if_pos (hmem.mpr hjN), if_pos hjN, hord, hN, TyIdx.idxOf_range hjN]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hjN)
    rw [if_neg (mt hmem.mp hjN), if_neg hjN, TyConsId.freeIdxs_of_inAnonOrder hord (by omega), hN,
      TyIdx.idxOf_map_of_injOn (List.mem_range.mpr (by omega)) (fun _ _ _ _ h => by simpa using h),
      TyIdx.idxOf_range (by omega), Nat.add_sub_cancel_left]

/-- The embedding of the type parameters of a source producing a constructor in anonymous order,
bound at the type parameters `A, …, A + N - 1` with its free type parameters from `B` on: the
`N` type parameters the constructor uses are shifted by `A`, and the free ones are shifted to
start at `B`.  Nothing is reordered. -/
theorem Source.ren_of_inAnonOrder (s : Source) (hord : s.fn.ty.InAnonOrder) {N : ℕ}
    (hN : s.fn.ty.arity = N) (A B : ℕ) {j : ℕ} (hj : j < s.arity) :
    s.ren ((List.range N).map (A + ·)) B j = if j < N then A + j else B + (j - N) := by
  rw [s.ren_of_inAnonOrder_sel hord hN _ B hj]
  split_ifs with hjN <;> simp [hjN]

/-- A type constructor bounded by `n` uses as many of the first `n` type parameters as it does
not leave free. -/
theorem TyConsId.arity_add_freeArity {c : TyConsId} {n : ℕ} (h : c.Bounded n) :
    c.arity + c.freeArity n = n := by
  have hperm : ((List.range n).filter (· ∈ c.params)).Perm c.params := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) (TyConsId.params_nodup c)]
    intro a
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun ha => ⟨h a ha, ha⟩⟩
  rw [TyConsId.arity, ← hperm.length_eq, TyConsId.freeArity, TyConsId.freeIdxs]
  have := List.length_eq_length_filter_add (l := List.range n) (fun a => decide (a ∈ c.params))
  rw [List.length_range] at this
  convert this.symm using 3
  simp

/-! ## Weaving the input values -/

theorem weaveVals_cons_pos {i : TyIdx} {p : PVar × TyConsId} (ps : List (PVar × TyConsId))
    (vs rs : List Val) (h : p.2 = .param i) :
    weaveVals i vs rs (p :: ps) = rs.headD .unit :: weaveVals i vs rs.tail ps := by
  rw [weaveVals, if_pos h]

theorem weaveVals_cons_neg {i : TyIdx} {p : PVar × TyConsId} (ps : List (PVar × TyConsId))
    (vs rs : List Val) (h : ¬ p.2 = .param i) :
    weaveVals i vs rs (p :: ps) = vs.headD .unit :: weaveVals i vs.tail rs ps := by
  rw [weaveVals, if_neg h]

@[simp] theorem length_weaveVals (i : TyIdx) (vs rs : List Val) (ps : List (PVar × TyConsId)) :
    (weaveVals i vs rs ps).length = ps.length := by
  induction ps generalizing vs rs with
  | nil => rfl
  | cons p ps ih => unfold weaveVals; split <;> simp [ih]

/-- Weaving only reads as many produced values as there are parameters carrying the pinned type
parameter; any missing one is the unit value. -/
theorem weaveVals_congr_rs (i : TyIdx) (ps : List (PVar × TyConsId)) (vs rs rs' : List Val)
    (h : ∀ k < (ps.filter fun p => p.2 == .param i).length, rs.getD k .unit = rs'.getD k .unit) :
    weaveVals i vs rs ps = weaveVals i vs rs' ps := by
  induction ps generalizing vs rs rs' with
  | nil => rfl
  | cons p ps ih =>
    unfold weaveVals
    split <;> rename_i hp
    · rw [List.filter_cons_of_pos (by simpa using hp), List.length_cons] at h
      congr 1
      · have := h 0 (by omega)
        revert this; cases rs <;> cases rs' <;> simp
      · exact ih _ _ _ fun k hk => by
          have := h (k + 1) (by omega)
          revert this; cases rs <;> cases rs' <;> simp
    · rw [List.filter_cons_of_neg (by simpa using hp)] at h
      rw [ih _ _ _ h]

namespace Source

variable {m : ℕ} {s : Source} {i : TyIdx} {τ : TyConsId} {srcs : List Source} {ςs : List Summary}

/-- The parameters of a source carrying the type parameter `i`. -/
def specParams (s : Source) (i : TyIdx) : List (PVar × TyConsId) :=
  s.fn.params.filter fun ⟨_, τ₀⟩ => τ₀ == .param i

/-- A source has as many parameters carrying a type parameter as that type parameter occurs
among the type constructors of its parameters. -/
theorem length_specParams : (s.specParams i).length = s.paramCount i := by
  rw [specParams, paramCount, FunTempl.paramCons, List.count_eq_countP, List.countP_map,
    ← List.countP_eq_length_filter]
  rfl

/-- The parameters of a source *not* carrying the type parameter `i`. -/
def restParams (s : Source) (i : TyIdx) : List (PVar × TyConsId) :=
  s.fn.params.filter fun ⟨_, τ₀⟩ => τ₀ != .param i

/-- The names of the parameters a specialisation let-binds. -/
def specVars (s : Source) (i : TyIdx) : List PVar := (s.specParams i).map (·.fst)
/-- The names of the parameters a specialisation keeps. -/
def restVars (s : Source) (i : TyIdx) : List PVar := (s.restParams i).map (·.fst)

/-- The type parameters prescribed for the supplied sources of a specialisation: for every
pinned parameter, the type parameters of the pinned constructor `τ`, placed at the position `i`
of the pinned type parameter. -/
def specSels (s : Source) (i : TyIdx) (τ : TyConsId) : List (List TyIdx) :=
  List.replicate (s.specParams i).length (τ.shiftTo i).params

/-- The parameters a specialisation binds sources to: those carrying the pinned type parameter,
now carrying the pinned constructor placed at the position of the pinned type parameter. -/
theorem pinnedParams_fst :
    (s.pinnedParams i τ).1 = (s.specParams i).map fun p => (p.1, τ.shiftTo i) := by
  simp [pinnedParams, List.partition_eq_filter_filter, specParams]

/-- The names of the parameters a specialisation binds sources to. -/
theorem pinnedParams_fst_names : (s.pinnedParams i τ).1.map Prod.fst = s.specVars i := by
  rw [pinnedParams_fst, List.map_map]
  rfl

/-- The type parameters of the type constructors of the parameters a specialisation binds
sources to are those prescribed for the supplied sources. -/
theorem pinnedParams_fst_sels :
    ((s.pinnedParams i τ).1.map Prod.snd).map TyConsId.params = s.specSels i τ := by
  rw [pinnedParams_fst, List.map_map, List.map_map, specSels]
  exact List.map_const' (l := s.specParams i) (b := (τ.shiftTo i).params)

/-- The parameters a specialisation keeps: those not carrying the pinned type parameter, with
their type constructors specialised. -/
theorem pinnedParams_snd :
    (s.pinnedParams i τ).2
      = (s.restParams i).map (fun p => (p.1, p.2.substCons (TyConsId.specSubst i τ))) := by
  simp only [pinnedParams, List.partition_eq_filter_filter, Prod.map_snd, restParams]
  congr 2

section BindSources

variable {N : ℕ} {rty : TyConsId}

/-- The parameters the bound sources contribute are those of `bindSourcesAux`, at the renaming
`PVar.freshen m` and, for every source, the selection of the type parameters of the type
constructor of the parameter it is bound to, whatever the body, variables and result type
constructor of the latter. -/
theorem boundParams_eq (t : TyArgs N → Expr) :
    ∀ (cons : List TyConsId) (srcs : List Source) (vars : List PVar) (base : ℕ),
      boundParams m cons base srcs
        = (bindSourcesAux t (PVar.freshen m) vars rty base (cons.map TyConsId.params) srcs).params
  | _, [], _, _ => rfl
  | cons, s :: srcs, vars, base => by
    rw [boundParams, Expr.bindSourcesAux_cons_params, ← List.map_tail,
      ← boundParams_eq t cons.tail srcs vars.tail]
    cases cons <;> rfl

/-- The sources contribute one parameter per parameter of theirs. -/
@[simp] theorem length_boundParams :
    ∀ (cons : List TyConsId) (srcs : List Source) (base : ℕ),
      (boundParams m cons base srcs).length = mergedValArity srcs
  | _, [], _ => rfl
  | cons, s :: srcs, base => by
    rw [boundParams, List.length_append, List.length_map, length_boundParams cons.tail srcs]
    rfl

/-- Let-binding a source in front of the remaining ones: its type arguments are those at the
type parameters of its type constructor followed by its own share of the free ones. -/
theorem bindSources_cons (types : TyArgs N) (body : Expr) (params : List (PVar × TyConsId))
    (s : Source) (srcs : List Source)
    (free : TyArgs (mergedFreeArity (s :: srcs))) (args : TeleArg (mergedTeleOf (s :: srcs))) :
    Expr.bindSources m types body params (s :: srcs) free args
      = .letIn (.named (params.headD ("unreachable", .unit)).1)
          ((s.fn.body.apply args.fst).apply
              (((types.reindex Ty.unit ((params.headD ("unreachable", .unit)).2.params.getD · 0)
                  (params.headD ("unreachable", .unit)).2.arity)
                |>.appendUniform (free.splitUniform s.freeArity _).1).reindex Ty.unit id s.arity)
            |>.bindAliases (PVar.freshen m srcs.length) s.fn.paramNames)
          (Expr.bindSources m types body params.tail srcs
            (free.splitUniform s.freeArity _).2 args.snd) :=
  rfl

/-- The type arguments a source naming its type parameters in the order of the anonymous form
of the constructor it produces is read at by blocks — a block `τTypes` holding the type arguments
at the positions `osel` the constructor's type parameters are bound to, followed by its own
block `own` of free ones, at the positions from `B` on — are those it is read at along the
embedding `Source.ren`. -/
theorem tyArgs_blocks {K : ℕ} (s : Source) (hord : s.fn.ty.InAnonOrder) (hK : s.fn.ty.arity = K)
    (hb : s.fn.ty.Bounded s.arity) (types : TyArgs N) (osel : List TyIdx) (B : ℕ)
    (τTypes : TyArgs K) (own : TyArgs s.freeArity)
    (hτ : ∀ j < K, τTypes.get j = types.get (osel.getD j 0))
    (hown : ∀ j < s.freeArity, own.get j = types.get (B + j)) :
    (τTypes.appendUniform own).reindex Ty.unit id s.arity = s.tyArgs osel B types := by
  have hlen : K + s.freeArity = s.arity := hK ▸ TyConsId.arity_add_freeArity hb
  refine TyArgs.ext fun j hj => ?_
  rw [Source.tyArgs, TyArgs.get_reindex (τs := types) hj, s.ren_of_inAnonOrder_sel hord hK osel B hj, TyArgs.get,
    TeleArg.toList_reindex_id _ _ hlen, TeleArg.toList_appendUniform]
  have hτlen : (TeleArg.toList τTypes).length = K := TeleArg.toList_length _
  rw [List.getD_eq_getElem?_getD]
  split_ifs with hjK
  · rw [List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    exact hτ j hjK
  · rw [List.getElem?_append_right (by omega), hτlen, ← List.getD_eq_getElem?_getD]
    exact hown (j - K) (by omega)

/-- Let-binding the sources in front of an expression is the body of `bindSourcesAux`, at the
renaming `PVar.freshen m`, the names of the parameters they are bound to and, for every source,
the selection of the type parameters of the type constructor of its parameter, as soon as every
source names its type parameters in the order of the anonymous form of the constructor it
produces, a constructor with as many type parameters as that of its parameter, and the block `free` holds the type
arguments of the free type parameters of the sources, from `base` on. -/
theorem bindSources_eq (t : TyArgs N → Expr) (types : TyArgs N) :
    ∀ (params : List (PVar × TyConsId)) (base : ℕ) (srcs : List Source)
      (free : TyArgs (mergedFreeArity srcs)) (args : TeleArg (mergedTeleOf srcs)),
      List.Forall₂ (fun s p => s.fn.ty.InAnonOrder ∧ s.fn.ty.arity = p.2.arity
        ∧ s.fn.ty.Bounded s.arity) srcs params →
      (∀ j < mergedFreeArity srcs, free.get j = types.get (base + j)) →
      Expr.bindSources m types (t types) params srcs free args
        = ((bindSourcesAux t (PVar.freshen m) (params.map Prod.fst) rty base
            ((params.map Prod.snd).map TyConsId.params) srcs).body.apply args).apply types
  | _, _, [], _, _, _, _ => by rw [Expr.bindSourcesAux_nil_body]; rfl
  | [], _, _ :: _, _, _, hfit, _ => by cases hfit
  | (x, τ) :: params, base, s :: srcs, free, args, hfit, hfree => by
    obtain ⟨⟨hord, hK, hb⟩, hfit⟩ := List.forall₂_cons.mp hfit
    have hsplit : ∀ j, TyArgs.get (free.splitUniform s.freeArity _).2 j
        = free.get (s.freeArity + j) := fun j => by
      rw [TyArgs.get, TyArgs.get, TeleArg.toList_splitUniform_right, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [bindSources_cons, Expr.bindSourcesAux_cons_body, List.map_cons, List.map_cons,
      List.map_cons, List.headD_cons, List.tail_cons, List.headD_cons, List.tail_cons,
      List.headD_cons, List.tail_cons,
      bindSources_eq t types params (base + s.freeArity) srcs _ args.snd hfit
        (fun j hj => by
          rw [hsplit, hfree _ (by rw [mergedFreeArity_cons]; omega), Nat.add_assoc]),
      tyArgs_blocks s hord hK hb types τ.params base _ _
        (fun j hj => TyArgs.get_reindex hj)
        (fun j hj => by
          rw [TyArgs.get, TeleArg.getD_toList_splitUniform_left _ _ hj, ← TyArgs.get,
            hfree _ (by rw [mergedFreeArity_cons]; omega)])]

end BindSources

@[simp] theorem specialise_ty :
    (specialise m s i τ ςs).fn.ty = s.fn.ty.substCons (TyConsId.specSubst i τ) := rfl

@[simp] theorem specialise_arity :
    (specialise m s i τ ςs).arity = s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src) := rfl

/-- The parameters of a specialised source, when one source is supplied per parameter carrying
the pinned type parameter: the parameters of `s` that are kept, with their type constructors
specialised, followed by the renamed parameters of the supplied sources. -/
theorem specialise_params
    (body : TyArgs (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src)) → Expr)
    (hlen : (ςs.map Summary.src).length = (s.specParams i).length) :
    (specialise m s i τ ςs).fn.params
      = (s.restParams i).map (fun p => (p.1, p.2.substCons (TyConsId.specSubst i τ)))
        ++ (bindSourcesAux body (PVar.freshen m) (s.specVars i)
            (s.fn.ty.substCons (TyConsId.specSubst i τ)) (s.arity - 1 + τ.arity) (s.specSels i τ)
            (ςs.map Summary.src)).params := by
  show (s.pinnedParams i τ).2 ++ boundParams m (List.replicate ςs.length (τ.shiftTo i)) _ _ = _
  rw [List.length_map] at hlen
  rw [pinnedParams_snd, boundParams_eq (rty := s.fn.ty.substCons (TyConsId.specSubst i τ)) body _ _
    (s.specVars i), List.map_replicate, hlen, specSels]
  rfl

/-- The type arguments the body of a source whose type parameter `i` is pinned to `τ` is read
at, inside the specialised source (`Source.specialise`), at the type arguments `types` of the
latter: the block of the first `i` and the block of the `s.arity - 1 - i` following the
`τ.arity` ones of `τ`, with `τ`, instantiated at the block of its own type parameters, inserted
in between. -/
def specTyArgs (s : Source) (i : TyIdx) (τ : TyConsId) {M : ℕ} (types : TyArgs M) :
    TyArgs s.arity :=
  let pinnedTy := τ.instantiate (types.block .unit i τ.arity).toList |>.getD .unit
  let ⟨before, after⟩ :=
    (types.block .unit 0 i, types.block .unit (i + τ.arity) (s.arity - 1 - i))
  (before.appendUniform (after.consUniform pinnedTy)).reindex Ty.unit id s.arity

/-- The body of a specialised source: the supplied sources are let-bound in front of the
body of `s`, which is run at the type arguments of `s` with `τ` pinned at position `i`, as soon
as one source is supplied per parameter carrying the pinned type parameter, and every supplied
source names its type parameters in the order of the anonymous form of the constructor it
produces, a constructor with as many type parameters as `τ`. -/
theorem specialise_body_apply (hlen : (ςs.map Summary.src).length = (s.specParams i).length)
    (hsrcs : ∀ s' ∈ ςs.map Summary.src,
      s'.fn.ty.InAnonOrder ∧ s'.fn.ty.arity = τ.arity ∧ s'.fn.ty.Bounded s'.arity)
    (args : TeleArg (specialise m s i τ ςs).teleOf)
    (types : TyArgs (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src))) :
    (((specialise m s i τ ςs).fn.body.apply args).apply types)
      = (((bindSourcesAux (N := s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src))
            (fun types => (s.fn.body.apply args.fst).apply (s.specTyArgs i τ types))
            (PVar.freshen m) (s.specVars i) (s.fn.ty.substCons (TyConsId.specSubst i τ))
            (s.arity - 1 + τ.arity) (s.specSels i τ) (ςs.map Summary.src)).body.apply args.snd).apply types) := by
  have hfit : List.Forall₂ (fun s' p => s'.fn.ty.InAnonOrder ∧ s'.fn.ty.arity = p.2.arity
      ∧ s'.fn.ty.Bounded s'.arity) (ςs.map Summary.src) (s.pinnedParams i τ).1 := by
    refine List.forall₂_iff_get.mpr ⟨by simp [pinnedParams_fst, hlen], fun k h₁ h₂ => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hsrcs _ (List.get_mem _ ⟨k, h₁⟩)
    refine ⟨h1, ?_, h3⟩
    simp only [List.get_eq_getElem, pinnedParams_fst, List.getElem_map]
    simpa using h2
  rw [← pinnedParams_fst_names (τ := τ), ← pinnedParams_fst_sels,
    ← bindSources_eq (fun types => (s.fn.body.apply args.fst).apply (s.specTyArgs i τ types))
      types _ _ (ςs.map Summary.src) _ args.snd hfit (fun j hj => by
        unfold TyArgs.get; exact TeleArg.getD_toList_block _ _ _ hj)]
  simp only [specialise, teleBind_apply]
  rfl

variable {Λ : Library} {own : TyConsId → ℕ → Val → Asrt.{0}} {off : TyConsId → ℕ}

/-! ## Properties

### The parameters of a specialised source -/

/-- The names a specialisation pins are, in order, parameter names of the source. -/
theorem specVars_sublist (s : Source) (i : TyIdx) :
    (s.specVars i).Sublist s.fn.paramNames :=
  List.filter_sublist.map Prod.fst

/-- The names a specialisation keeps are, in order, parameter names of the source. -/
theorem restVars_sublist (s : Source) (i : TyIdx) :
    (s.restVars i).Sublist s.fn.paramNames :=
  List.filter_sublist.map Prod.fst

/-- A specialisation splits the parameters of a source into the ones it keeps and the ones it
let-binds. -/
theorem length_restParams_add_specParams (s : Source) (i : TyIdx) :
    (s.restParams i).length + (s.specParams i).length = s.fn.params.length := by
  rw [restParams, specParams, Nat.add_comm,
    List.length_eq_length_filter_add (l := s.fn.params) (fun p => p.2 == .param i)]
  congr 2

/-- A specialisation keeps and pins disjoint sets of names. -/
theorem restVars_notMem_specVars (hdup : s.fn.paramNames.Nodup) {x : PVar}
    (hx : x ∈ s.restVars i) : x ∉ s.specVars i := by
  intro hx'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  obtain ⟨q', hq', hqq⟩ := List.mem_map.mp hx'
  obtain rfl :=
    List.inj_on_of_nodup_map hdup (List.mem_filter.mp hq').1 (List.mem_filter.mp hq).1 hqq
  simp only [restParams, specParams, List.mem_filter, bne_iff_ne, beq_iff_eq] at hq hq'
  exact hq.2 hq'.2

/-- The parameter names of a specialised source: the names of the parameters that are kept,
followed by the renamed parameter names of the supplied sources. -/
theorem specialise_paramNames
    (body : TyArgs (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src)) → Expr)
    (hlen : (ςs.map Summary.src).length = (s.specParams i).length) :
    (specialise m s i τ ςs).fn.paramNames
      = s.restVars i
        ++ (bindSourcesAux body (PVar.freshen m) (s.specVars i)
            (s.fn.ty.substCons (TyConsId.specSubst i τ)) (s.arity - 1 + τ.arity) (s.specSels i τ)
            (ςs.map Summary.src)).paramNames := by
  rw [FunTempl.paramNames, specialise_params body hlen, List.map_append,
    FunTempl.paramNames, restVars, List.map_map]
  rfl

/-- The signature of a specialised source: the parameters that are kept, at their specialised
types, followed by the signature of the merged supplied sources. -/
theorem specialise_sig (body : TyArgs (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src)) → Expr)
    (hlen : (ςs.map Summary.src).length = (s.specParams i).length)
    (types : TyArgs (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src))) :
    (specialise m s i τ ςs).fn.sig.apply types
      = (s.restParams i).map (fun p =>
            (p.1, (p.2.substCons (TyConsId.specSubst i τ)).concretise types))
        ++ (bindSourcesAux body (PVar.freshen m) (s.specVars i)
            (s.fn.ty.substCons (TyConsId.specSubst i τ)) (s.arity - 1 + τ.arity) (s.specSels i τ)
            (ςs.map Summary.src)).sig.apply types := by
  rw [FunTempl.sig_apply_eq_map, FunTempl.sig_apply_eq_map, specialise_params body hlen,
    List.map_append, List.map_map]
  rfl

/-! ### The type parameters prescribed for the supplied sources -/

/-- The type parameters prescribed for the supplied sources are usable: every supplied source
is prescribed the same type parameters `o`, all of them bound before the free type parameters
of the supplied sources start, and there are as many of them as the type constructor each
supplied source produces uses. -/
theorem selsOk_replicate (o : List TyIdx) {k : ℕ} (hk : ∀ j ∈ o, j < k) :
    ∀ (srcs : List Source) (L base : ℕ), k ≤ base → srcs.length ≤ L →
      (∀ s' ∈ srcs, s'.tyArity ≤ o.length) →
      Source.SelsOk srcs (List.replicate L o) base
  | [], _, _, _, _, _ => trivial
  | s' :: srcs, L, base, hbase, hlen, harity => by
      obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by simp at hlen; omega⟩
      simp only [SelsOk, List.replicate_succ, List.headD_cons, List.tail_cons]
      exact ⟨fun j hj => (hk j hj).trans_le hbase, harity s' List.mem_cons_self,
        selsOk_replicate o hk srcs L _ (hbase.trans (Nat.le_add_right _ _)) (by simpa using hlen)
          fun s'' hs'' => harity s'' (List.mem_cons_of_mem _ hs'')⟩

/-- The types the supplied sources produce: every supplied source typechecks and produces a
constructor matching `C`, and is prescribed the type parameters of `C`, so it produces `C`
instantiated at the type arguments of the template binding it. -/
theorem resTys_replicate {N : ℕ} (C : TyConsId) (types : TyArgs N) :
    ∀ (srcs : List Source) (L base : ℕ), srcs.length ≤ L →
      (∀ s' ∈ srcs, s'.Typechecks Λ) → (∀ s' ∈ srcs, s'.fn.ty.Match C) →
      Source.resTys srcs (List.replicate L C.params) base types
        = List.replicate srcs.length (C.concretise types)
  | [], _, _, _, _, _ => rfl
  | s' :: srcs, L, base, hlen, htc, hmatch => by
      obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by simp at hlen; omega⟩
      rw [Source.resTys_cons, List.replicate_succ, List.headD_cons, List.tail_cons,
        resTys_replicate C types srcs L _ (by simpa using hlen)
          (fun s'' hs'' => htc s'' (List.mem_cons_of_mem _ hs''))
          (fun s'' hs'' => hmatch s'' (List.mem_cons_of_mem _ hs'')),
        (htc s' List.mem_cons_self).resTy_apply_eq, Source.resTyAt, Source.ren,
        TyConsId.rename_mergeRen (hmatch s' List.mem_cons_self), List.length_cons,
        List.replicate_succ]

/-! ### Substituting the input values of a specialised source -/

/-- Substituting the input values of a specialised source, on an arbitrary list of
parameters. -/
theorem substs_weaveVals_aux (i : TyIdx) (ps : List (PVar × TyConsId)) (e : Expr)
    (rs vs : List Val) (hdup : (ps.map Prod.fst).Nodup)
    (hrs : rs.length = (ps.filter fun p => p.2 == TyConsId.param i).length)
    (hvs : vs.length = (ps.filter fun p => p.2 != TyConsId.param i).length) :
    e.substs (ps.map Prod.fst) (Term.ofVals (weaveVals i vs rs ps))
      = (e.substs ((ps.filter fun p => p.2 != TyConsId.param i).map Prod.fst)
            (Term.ofVals vs)).substs
          ((ps.filter fun p => p.2 == TyConsId.param i).map Prod.fst) (Term.ofVals rs) := by
  induction ps generalizing e rs vs with
  | nil => simp_all
  | cons p ps ih =>
    obtain ⟨hp, hdup⟩ := List.nodup_cons.mp hdup
    have hnotmem (f : PVar × TyConsId → Bool) : p.1 ∉ (ps.filter f).map Prod.fst :=
      fun hmem => hp ((List.filter_sublist.map Prod.fst).subset hmem)
    by_cases h : p.2 = TyConsId.param i <;>
      simp only [List.filter_cons, h, beq_iff_eq, bne_iff_ne, ne_eq, not_true_eq_false,
        not_false_eq_true, ite_true, ite_false] at hrs hvs ⊢
    · cases rs with
      | nil => simp at hrs
      | cons r rs =>
        rw [weaveVals_cons_pos ps vs _ h, List.map_cons, Term.ofVals_cons, Expr.substs_cons,
          List.headD_cons, List.tail_cons, ih _ rs vs hdup (by simpa using hrs) hvs, List.map_cons,
          Term.ofVals_cons, Expr.substs_cons, Expr.substTerm_substs_comm (hnotmem _)]
    · cases vs with
      | nil => simp at hvs
      | cons v vs =>
        rw [weaveVals_cons_neg ps _ rs h, List.map_cons, Term.ofVals_cons, Expr.substs_cons,
          List.headD_cons, List.tail_cons, ih _ rs vs hdup hrs (by simpa using hvs), List.map_cons,
          Term.ofVals_cons, Expr.substs_cons]

/-- Substituting the input values of a specialised source into the body of the source it
specialises: the values the let-bound sources produce are substituted at the parameters that
were pinned, and the input values of the specialised source at the others. -/
theorem substs_weaveVals (e : Expr) (hdup : s.fn.paramNames.Nodup)
    (rs vs : List Val) (hrs : rs.length = (s.specParams i).length)
    (hvs : vs.length = (s.restParams i).length) :
    e.substs s.fn.paramNames (Term.ofVals (weaveVals i vs rs s.fn.params))
      = (e.substs (s.restVars i) (Term.ofVals vs)).substs (s.specVars i) (Term.ofVals rs) :=
  substs_weaveVals_aux i s.fn.params e rs vs hdup hrs hvs

/-! ### Validity and typechecking -/

private theorem specIdx_lt {i j n : ℕ} (hj : j < n) (hi : i < n) (hne : ¬ j = i) :
    (if j < i then j else j - 1) < n - 1 := by
  split <;> omega

/-- The result type constructor of a specialised source only uses the type parameters it
has. -/
theorem specialise_ty_bounded (hs : s.fn.Valid) (hi : i < s.arity) :
    (s.fn.ty.substCons (TyConsId.specSubst i τ)).Bounded
      (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src)) := fun j hj =>
  Nat.lt_of_lt_of_le (hs.2.specSubst hi j hj) (Nat.le_add_right _ _)

/-- The type parameters prescribed for the supplied sources are usable, as soon as the type
constructor every supplied source produces matches the pinned one. -/
theorem selsOk_specSels (hi : i < s.arity)
    (hlen : (ςs.map Summary.src).length = (s.specParams i).length)
    (hmatch : ∀ s' ∈ (ςs.map Summary.src), s'.fn.ty.Match τ) :
    Source.SelsOk (ςs.map Summary.src) (s.specSels i τ) (s.arity - 1 + τ.arity) :=
  selsOk_replicate _ (fun _ hj => (TyConsId.mem_params_shiftTo.mp hj).2) (ςs.map Summary.src) _ _
    (Nat.add_le_add_right (Nat.le_sub_one_of_lt hi) _)
    (le_of_eq hlen) fun s' hs' => by
      rw [Source.tyArity, (hmatch s' hs').arity_eq, ← TyConsId.arity_shiftTo τ i]
      rfl

/-- A specialised source is structurally valid: the parameters it keeps still carry bare type
parameters, at their shifted positions, and the parameters of the supplied sources are their
own, renamed apart. -/
theorem specialise_valid (hs : s.fn.Valid) (hi : i < s.arity)
    (hok : ∀ s' ∈ (ςs.map Summary.src), s'.Ok Λ) (hsel : Source.SelsOk (ςs.map Summary.src) (s.specSels i τ) (s.arity - 1 + τ.arity))
    (hlen : (ςs.map Summary.src).length = (s.specParams i).length) :
    (specialise m s i τ ςs).fn.Valid := by
  have hrty : (s.fn.ty.substCons (TyConsId.specSubst i τ)).Bounded
      (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src)) := specialise_ty_bounded hs hi
  obtain ⟨hvalid, -⟩ :=
    Expr.bindSourcesAux_spec (Λ := Λ) (m := m) PVar.freshen_spec hrty (ςs.map Summary.src) (s.specVars i)
      (s.arity - 1 + τ.arity) (s.specSels i τ) (fun _ => .val .unit)
      (TeleArg.replicate _ Ty.unit) hok hsel (le_refl _)
  refine ⟨fun p hp => ?_, hrty⟩
  rw [specialise_params (fun _ => .val .unit) hlen, List.mem_append] at hp
  rcases hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [restParams, List.mem_filter] at hq
    obtain ⟨j, hj, hq2⟩ := hs.1 q hq.1
    have hne : (j : ℕ) ≠ i := fun h => by simp [hq2, h] at hq
    refine ⟨_, (TyConsId.keptIdx_lt (i := i) (k := τ.arity) (specIdx_lt hj hi hne)).trans_le
      (Nat.le_add_right _ _), ?_⟩
    rw [hq2, TyConsId.substCons_param, TyConsId.specSubst, if_neg hne]
  · exact hvalid.1 p hp

/-- The type arguments of a source whose type parameter `i` is pinned to `τ`, read off the
type arguments of the specialised source, for `τ` in anonymous form: the pinned type — `τ`
instantiated at the block of its type parameters — is the concretisation of `τ` shifted to `i`,
inserted at position `i` among the kept type arguments, read off at their positions
(`TyConsId.keptIdx`). -/
theorem specTyArgs_eq (hτ : τ.anon = τ) (hi : i < s.arity) {M : ℕ} (types : TyArgs M) :
    s.specTyArgs i τ types
      = TeleArg.insertUniformPred ((τ.shiftTo i).concretise types) i
          (TeleArg.reindex Ty.unit (TyConsId.keptIdx i τ.arity) (s.arity - 1) types) := by
  refine TyArgs.ext fun j hj => ?_
  rw [TyArgs.get, specTyArgs, TeleArg.getD_toList_arrange _ types _ τ.arity hi j, TyArgs.get,
    TeleArg.getD_toList_insertUniformPred _ _ i hi _ j]
  by_cases hji : j = i
  · have hb : τ.Bounded τ.arity := by
      have := TyConsId.anon_bounded τ; rwa [hτ] at this
    rw [if_pos hji, if_pos hji, TyConsId.instantiate_toList_getD hb, TyConsId.concretise,
      TyConsId.concretise, TyConsId.shiftTo, hτ, TyConsId.subst_rename]
    refine TyConsId.subst_congr _ fun k hk => ?_
    rw [Function.comp_apply]
    exact TeleArg.getD_toList_block _ _ _ (hb k hk)
  · rw [if_neg hji, if_neg hji, if_pos hj, ← TyArgs.get]
    show _ = TyArgs.get (TeleArg.reindex Ty.unit (TyConsId.keptIdx i τ.arity) (s.arity - 1) types) _
    by_cases hlt : j < i
    · rw [if_pos hlt, if_pos hlt, TyArgs.get_reindex (hlt.trans_le (Nat.le_sub_one_of_lt hi)),
        TyConsId.keptIdx, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt, TyArgs.get_reindex (Nat.sub_lt_sub_right (by omega) hj),
        TyConsId.keptIdx, if_neg (by omega)]

/-- Instantiating a bounded constructor whose type parameter `i` is pinned to `τ` at the type
arguments of a specialised source is instantiating the constructor itself at the type
arguments of the source it specialises. -/
theorem specTyArgs_concretise (hτ : τ.anon = τ) {c : TyConsId} (hc : c.Bounded s.arity)
    (hi : i < s.arity)
    {M : ℕ} (types : TyArgs M) :
    (c.substCons (TyConsId.specSubst i τ)).concretise types
      = c.concretise (s.specTyArgs i τ types) := by
  rw [specTyArgs_eq hτ hi]
  exact TyConsId.concretise_substCons_specSubst hc hi τ types

/-- The type arguments of a specialised source carry the pinned type at the pinned
position. -/
theorem specTyArgs_get_self (hτ : τ.anon = τ) (hi : i < s.arity) {M : ℕ} (types : TyArgs M) :
    TyArgs.get (s.specTyArgs i τ types) i = (τ.shiftTo i).concretise types := by
  rw [specTyArgs_eq hτ hi, TyArgs.get, TeleArg.getD_toList_insertUniformPred _ Ty.unit i hi _ i,
    if_pos rfl]

/-- Acceptable sources in anonymous order producing a constructor matching `τ` use as many
type parameters as `τ`, and only their own. -/
theorem srcs_inAnonOrder {srcs : List Source}
    (hok : ∀ s' ∈ srcs, s'.Ok Λ) (hmatch : ∀ s' ∈ srcs, s'.fn.ty.Match τ)
    (hord : ∀ s' ∈ srcs, s'.fn.ty.InAnonOrder) :
    ∀ s' ∈ srcs, s'.fn.ty.InAnonOrder ∧ s'.fn.ty.arity = τ.arity ∧ s'.fn.ty.Bounded s'.arity :=
  fun s' hs' => ⟨hord s' hs', (hmatch s' hs').arity_eq, (hok s' hs').typechecks.ty_bounded⟩

/-- A specialised source typechecks: its body binds the bodies of the supplied sources — each
of which produces the type constructor the specialisation pins, at the type parameters it
contributes — to the parameters that carried the pinned type parameter, and ends in the body
of the source it specialises, which is well typed there. -/
theorem specialise_typechecks (hs : s.Typechecks Λ) (hi : i < s.arity) (hτ : τ.anon = τ)
    (hok : ∀ s' ∈ (ςs.map Summary.src), s'.Ok Λ) (hmatch : ∀ s' ∈ (ςs.map Summary.src), s'.fn.ty.Match τ)
    (hord : ∀ s' ∈ (ςs.map Summary.src), s'.fn.ty.InAnonOrder)
    (hvarlen : ∀ y ∈ s.fn.paramNames, y.length ≤ m)
    (hsrclen : ∀ s' ∈ (ςs.map Summary.src), ∀ y ∈ s'.fn.paramNames, y.length ≤ m)
    (hdup : s.fn.paramNames.Nodup)
    (hlen : (ςs.map Summary.src).length = (s.specParams i).length) :
    (specialise m s i τ ςs).Typechecks Λ := by
  have hvalid : s.fn.Valid := hs.src_valid
  have hsel := selsOk_specSels (s := s) (i := i) hi hlen hmatch
  have hrty : (s.fn.ty.substCons (TyConsId.specSubst i τ)).Bounded
      (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src)) :=
    specialise_ty_bounded hvalid hi
  have hRsub := restVars_sublist s i
  have hVlen : ∀ y ∈ s.specVars i, y.length ≤ m :=
    fun y hy => hvarlen y ((specVars_sublist s i).subset hy)
  have hVlen' : (s.specVars i).length = (ςs.map Summary.src).length := by
    rw [specVars, List.length_map, hlen]
  refine ⟨specialise_valid (m := m) hvalid hi hok hsel hlen, fun types args => ?_⟩
  let body (ts : TyArgs (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src))) :=
    (s.fn.body.apply args.fst).apply (s.specTyArgs i τ ts)
  obtain ⟨-, -, hfreshP, hnodupP, hsafeT⟩ :=
    Expr.bindSourcesAux_spec (Λ := Λ) (m := m) PVar.freshen_spec hrty (ςs.map Summary.src)
      (s.specVars i) (s.arity - 1 + τ.arity) (s.specSels i τ) body types hok hsel (le_refl _)
  have hnodup : (specialise m s i τ ςs).fn.paramNames.Nodup := by
    rw [specialise_paramNames (m := m) (τ := τ) body hlen]
    refine List.nodup_append.mpr ⟨hdup.sublist hRsub, hnodupP, fun y hy x hx => ?_⟩
    obtain ⟨j, z, -, rfl⟩ := hfreshP x hx
    exact PVar.freshen_spec.ne_short (hvarlen _ (hRsub.subset hy))
  have hsigdup : (((specialise m s i τ ςs).fn.sig.apply types).map Prod.fst).Nodup := by
    rwa [FunTempl.sig_map_fst]
  refine ⟨?safe, rfl, ?nodup⟩
  case nodup =>
    simpa only [FunImpl.ParamsNodup, FunImpl.paramNames, FunTempl.concretise_params,
      FunTempl.sig_map_fst] using hnodup
  case safe =>
    simp only [FunTempl.concretise_params, FunTempl.concretise_body, FunTempl.concretise_ty,
      FunImpl.paramNames]
    rw [specialise_body_apply hlen (srcs_inAnonOrder hok hmatch hord)]
    refine hsafeT args.snd _ _ hsrclen hVlen hVlen'.ge (fun y τy hmem => ?_) ?hcall
    · refine VarCtx.from_lookup_some hsigdup ?_
      rw [specialise_sig body hlen]
      exact List.mem_append_right _ hmem
    case hcall =>
      have hmatch' : ∀ s' ∈ (ςs.map Summary.src), s'.fn.ty.Match (τ.shiftTo i) :=
        fun s' hs' => (hmatch s' hs').trans (TyConsId.shiftTo_match τ _).symm
      rw [specSels, Source.resTys_replicate (Λ := Λ) _ types (ςs.map Summary.src) _ _ (le_of_eq hlen)
          (fun s' hs' => (hok s' hs').typechecks) hmatch',
        FunTempl.resTy_apply, specialise_ty, specTyArgs_concretise hτ hvalid.2 hi]
      obtain ⟨hsafe_s, -, -⟩ := hs.concretise_typechecks args.fst (s.specTyArgs i τ types)
      rw [FunTempl.concretise_params, FunTempl.concretise_body, FunTempl.concretise_ty,
        FunImpl.paramNames, FunTempl.resTy_apply] at hsafe_s
      refine safeProgram_subset hsafe_s (VarCtx.from_subset ?_)
      intro x σ hmem
      rw [FunTempl.concretise_params, FunTempl.sig_apply_eq_map] at hmem
      obtain ⟨p, hp, heq⟩ := List.mem_map.mp hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      by_cases hpi : p.2 = TyConsId.param i
      · rw [hpi, TyConsId.concretise_param, specTyArgs_get_self hτ hi]
        exact VarCtx.extend_lookup_replicate hVlen'.le
          (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp [hpi]⟩, rfl⟩)
      · have hmemR : p.1 ∈ s.restVars i :=
          List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simpa using hpi⟩, rfl⟩
        rw [VarCtx.extend_lookup_of_notMem _ (restVars_notMem_specVars hdup hmemR)]
        refine VarCtx.from_lookup_some hsigdup ?_
        rw [specialise_sig body hlen]
        refine List.mem_append_left _ (List.mem_map.mpr ⟨p, ?_, ?_⟩)
        · exact List.mem_filter.mpr ⟨hp, by simpa using hpi⟩
        · rw [specTyArgs_concretise hτ (hvalid.bounded.param hp) hi]

/-! ### The behaviour of a specialised source -/

/-- The body of a specialised source, run on the resources its parameters require,
reproduces the behaviour of the body of the source it specialises on the values the
let-bound sources produce. -/
theorem specialise_frameStep
    (hi : i < s.arity) (hs : s.Ok Λ)
    (hok : ∀ s' ∈ (ςs.map Summary.src), s'.Ok Λ)
    (hmatch : ∀ s' ∈ (ςs.map Summary.src), s'.fn.ty.Match τ)
    (hord : ∀ s' ∈ (ςs.map Summary.src), s'.fn.ty.InAnonOrder)
    (hsel : Source.SelsOk (ςs.map Summary.src) (s.specSels i τ) (s.arity - 1 + τ.arity))
    (hsrclen : ∀ s' ∈ (ςs.map Summary.src), ∀ y ∈ s'.fn.paramNames, y.length ≤ m)
    (hvarlen : ∀ y ∈ s.fn.paramNames, y.length ≤ m)
    (hdup : s.fn.paramNames.Nodup)
    (hlen : (ςs.map Summary.src).length = (s.specParams i).length)
    (syms : TeleArg s.teleOf) (syms' : TeleArg (mergedTeleOf (ςs.map Summary.src)))
    (types : TyArgs (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src)))
    (boundVals : TeleArg (Tele.uniform Val (mergedValArity (ςs.map Summary.src))))
    (restVals : List Val) (rs : List Val) (g hF h h' : Heap) (εₛ : Exit)
    (hrestlen : restVals.length = (s.restParams i).length)
    (hdisj : hF ##ₘ h)
    (hruns : Source.Runs Λ own types (ςs.map Summary.src) off (s.specSels i τ) (s.arity - 1 + τ.arity) syms'
      boundVals rs g h)
    (hstep : Λ ⊢ ⟨hF ∪ h |
        ((s.fn.body.apply syms).apply (s.specTyArgs i τ types)).substs s.fn.paramNames
          (Term.ofVals (weaveVals i restVals rs s.fn.params))⟩ ⇓ᵢ ⟨h' | εₛ⟩) :
    HProp g (FunTempl.ownValsAt own off
            (bindSourcesAux (N := s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src))
              (fun _ => .val .unit) (PVar.freshen m) (s.specVars i)
              (s.fn.ty.substCons (TyConsId.specSubst i τ)) (s.arity - 1 + τ.arity) (s.specSels i τ)
              (ςs.map Summary.src)).paramCons boundVals.toList)
      ∧ hF ##ₘ g
      ∧ Λ ⊢ ⟨hF ∪ g |
          (((specialise m s i τ ςs).fn.body.apply (syms.app syms')).apply types).substs
            (specialise m s i τ ςs).fn.paramNames
            (Term.ofVals (restVals ++ boundVals.toList))⟩ ⇓ᵢ ⟨h' | εₛ⟩ := by
  have hrty : (s.fn.ty.substCons (TyConsId.specSubst i τ)).Bounded
      (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src)) :=
    specialise_ty_bounded hs.src_valid hi
  have hVsub := specVars_sublist s i
  have hRsub := restVars_sublist s i
  have hVlen : ∀ y ∈ s.specVars i, y.length ≤ m := fun y hy => hvarlen y (hVsub.subset hy)
  have hRlen : ∀ y ∈ s.restVars i, y.length ≤ m := fun y hy => hvarlen y (hRsub.subset hy)
  have hVnodup : (s.specVars i).Nodup := List.Nodup.sublist hVsub hdup
  have hVle : (ςs.map Summary.src).length ≤ (s.specVars i).length := by
    simp only [specVars, List.length_map] at hlen ⊢; omega
  have hrslen : rs.length = (s.specParams i).length := by
    rw [Source.runs_length _ _ _ _ _ _ _ _ _ hruns, hlen]
  have hrestvars : (s.restVars i).length = restVals.length := by
    rw [restVars, List.length_map, hrestlen]
  -- The body the merged sources are bound in front of.
  let body (ts : TyArgs (s.arity - 1 + τ.arity + mergedFreeArity (ςs.map Summary.src))) :=
    ((s.fn.body.apply syms).apply (s.specTyArgs i τ ts)).substs (s.restVars i)
      (Term.ofVals restVals)
  have hbodyclosed (ts) : (body ts).Closed {y : PVar | y.length ≤ m} := by
    refine Expr.Closed.substs_erase (X := {y : PVar | y.length ≤ m}) ?_ hrestvars
    exact Expr.Closed.mono (hs.body_closed syms (s.specTyArgs i τ ts))
      fun z hz => Or.inl (hvarlen z hz)
  rw [substs_weaveVals _ hdup rs restVals hrslen hrestlen] at hstep
  obtain ⟨hprop, hdisjg, hstep'⟩ :=
    Expr.bindSourcesAux_frameStep (rty := s.fn.ty.substCons (TyConsId.specSubst i τ))
      PVar.freshen_spec hrty (ςs.map Summary.src) (s.specVars i) off (s.arity - 1 + τ.arity) (s.specSels i τ)
      body syms' types boundVals rs g hF h h' εₛ hok hsrclen hVlen hVnodup hVle hbodyclosed
      hsel (le_refl _) hdisj hruns hstep
  refine ⟨by rwa [Expr.bindSourcesAux_paramCons_tail_irrel _ body], hdisjg, ?_⟩
  rw [specialise_body_apply hlen (srcs_inAnonOrder hok hmatch hord),
    specialise_paramNames body hlen, Term.ofVals_append,
    Expr.substs_append _ (by rw [Term.ofVals, List.length_map]; exact hrestvars),
    TeleArg.fst_append, TeleArg.snd_append,
    Expr.bindSourcesAux_substs PVar.freshen_spec (ςs.map Summary.src) (s.specVars i)
      (s.arity - 1 + τ.arity) (s.specSels i τ) syms' types hok hVle (s.restVars i) restVals
      (fun ts => (s.fn.body.apply syms).apply (s.specTyArgs i τ ts))
      (fun x hx => restVars_notMem_specVars hdup hx) hRlen]
  exact hstep'

end Source

/-! ### The resources a specialisation requires of the input values -/

/-- The resources the input values of a source own when it is specialised, read through the
typed subvariant arguments `S` and ranked from the offsets `off`: at a parameter carrying the
pinned type parameter, the resources required of the value `rs` the source let-bound there
produces; at any other parameter, the resources required of the corresponding input value
`vs` of the specialised source. -/
def Source.specPreVals (Λ : Library) (i : TyIdx) {n : ℕ} (S : SubvArgs.{0} n) :
    (TyConsId → ℕ) → List (PVar × TyConsId) → List Val → List Val → Asrt.{0}
  | _, [], _, _ => .emp
  | off, p :: ps, rs, vs =>
      if p.2 = .param i then
        p.2.ownsAt Λ S (off p.2) (rs.headD .unit)
          ∗ specPreVals Λ i S (TyConsId.bumpOff off p.2) ps rs.tail vs
      else
        p.2.ownsAt Λ S (off p.2) (vs.headD .unit)
          ∗ specPreVals Λ i S (TyConsId.bumpOff off p.2) ps rs vs.tail

/-- The resources a specialisation requires of the input values, split into the resources the
let-bound sources produce — one per pinned parameter, described by the subvariant of its rank
— and the resources of the input values that are kept.

The hypothesis `hos` says that the subvariants the typed subvariant supplied for the pinned
type parameter gives, from the rank the pinned parameters start at, are the assertions `os`,
one per pinned parameter. -/
theorem Source.hProp_specPreVals_split {Λ : Library} {i : TyIdx} {N : ℕ} (S : SubvArgs.{0} N) :
    ∀ (ps : List (PVar × TyConsId)) (os : List (Val → Asrt.{0})) (rs vs : List Val)
      (off : TyConsId → ℕ) (h : Heap),
      rs.length = (ps.filter fun p => p.2 == TyConsId.param i).length →
      vs.length = (ps.filter fun p => p.2 != TyConsId.param i).length →
      os.length = rs.length →
      (∀ (k : ℕ) (hk : k < os.length) (v : Val),
        (S.get i).get Λ (off (.param i) + k) v = os[k] v) →
      HProp h (Source.specPreVals Λ i S off ps rs vs) →
      HProp h ((Asrt.iter (rs.zip os) fun q => q.2 q.1) ∗
        FunTempl.ownValsAt (fun C => C.ownsAt Λ S) off
          ((ps.filter fun p => p.2 != TyConsId.param i).map Prod.snd) vs) := by
  intro ps
  induction ps with
  | nil =>
    intro os rs vs off h hrs hvs hos _ hprop
    simp only [List.filter_nil, List.length_nil, List.length_eq_zero_iff] at hrs hvs
    subst hrs hvs
    obtain rfl : os = [] := List.eq_nil_of_length_eq_zero hos
    obtain rfl : h = ∅ := hprop
    exact ⟨∅, ∅, (PFun.empty_union ∅).symm, PFun.disjoint_empty_left _, rfl, rfl⟩
  | cons p ps ih =>
    intro os rs vs off h hrs hvs hos hread hprop
    by_cases hp : p.2 = TyConsId.param i <;>
      simp only [List.filter_cons, hp, beq_iff_eq, bne_iff_ne, ne_eq, not_true_eq_false,
        not_false_eq_true, ite_true, ite_false, List.length_cons] at hrs hvs ⊢ <;>
      rw [Source.specPreVals] at hprop <;> split_ifs at hprop <;>
      obtain ⟨h₁, h₂, rfl, hdisj, hhead, htail⟩ := hprop
    · obtain _ | ⟨r, rs⟩ := rs; · simp at hrs
      obtain _ | ⟨o, os⟩ := os; · simp at hos
      have hb : TyConsId.bumpOff off p.2 (TyConsId.param i) = off (.param i) + 1 := by
        simp [hp, TyConsId.bumpOff]
      obtain ⟨h₃, h₄, rfl, hdisj34, hA, hB⟩ :=
        ih os rs vs (TyConsId.bumpOff off p.2) h₂ (by simpa using hrs) hvs (by simpa using hos)
          (fun k hk v => by
            rw [hb, Nat.add_assoc, Nat.add_comm 1 k]; exact hread (k + 1) (by simpa using hk) v)
          htail
      rw [PFun.disjoint_union_right] at hdisj
      rw [FunTempl.ownValsAt_congr_off _ _ _ fun C hC => ?_] at hB
      · refine ⟨h₁ ∪ h₃, h₄, (PFun.union_assoc ..).symm,
          PFun.disjoint_union_left.mpr ⟨hdisj.2, hdisj34⟩, ⟨h₁, h₃, rfl, hdisj.1, ?_, hA⟩, hB⟩
        rw [hp, TyConsId.ownsAt_param] at hhead
        show HProp h₁ (o r)
        exact (by simpa using hread 0 (Nat.succ_pos _) r) ▸ hhead
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hC
        rw [hp, TyConsId.bumpOff]
        exact if_neg (by simpa using List.of_mem_filter hq)
    · obtain _ | ⟨v, vs⟩ := vs; · simp at hvs
      have hb : TyConsId.bumpOff off p.2 (TyConsId.param i) = off (.param i) := by
        simp [TyConsId.bumpOff, Ne.symm hp]
      obtain ⟨h₃, h₄, rfl, hdisj34, hA, hB⟩ :=
        ih os rs vs (TyConsId.bumpOff off p.2) h₂ hrs (by simpa using hvs) hos
          (fun k hk w => hb ▸ hread k hk w) htail
      rw [PFun.disjoint_union_right] at hdisj
      refine ⟨h₃, h₁ ∪ h₄, ?_, PFun.disjoint_union_right.mpr ⟨hdisj.1.symm, hdisj34⟩, hA,
        h₁, h₄, rfl, hdisj.2, hhead, hB⟩
      rw [← PFun.union_assoc, PFun.union_comm hdisj.1, PFun.union_assoc]

/-- The resources a summary requires of its input values *are* the resources a specialisation
requires of them: the two assertions only differ in how the input values are presented — all
of them at once, or the pinned ones apart from the ones the specialisation keeps. -/
theorem Source.ownValsAt_weaveVals {Λ : Library} {i : TyIdx} {n : ℕ} (S : SubvArgs.{0} n) :
    ∀ (ps : List (PVar × TyConsId)) (rs vs : List Val) (off : TyConsId → ℕ),
      FunTempl.ownValsAt (fun C => C.ownsAt Λ S) off (ps.map Prod.snd)
          (weaveVals i vs rs ps)
        = Source.specPreVals Λ i S off ps rs vs := by
  intro ps
  induction ps with
  | nil => intro rs vs off; rw [List.map_nil, FunTempl.ownValsAt_nil_cons, Source.specPreVals]
  | cons p ps ih =>
    intro rs vs off
    unfold weaveVals
    rw [Source.specPreVals]
    split <;> rw [List.map_cons, FunTempl.ownValsAt_cons, ih]

/-- The type constructors of the parameters of a merge of sources, bound from `base` on and
prescribed type parameters satisfying `P`, every type parameter from `base` on satisfying `P`
too: every one of them is a type parameter of the merge satisfying `P`. -/
theorem Expr.mem_bindSourcesAux_paramCons_of {N : ℕ} {body : TyArgs N → Expr}
    {rename : ℕ → PVar → PVar} {rty : TyConsId} (P : ℕ → Prop) :
    ∀ (srcs : List Source) (vars : List PVar) (base : ℕ) (osels : List (List TyIdx)),
      (∀ k, base ≤ k → P k) → (∀ o ∈ osels, ∀ j ∈ o, P j) → Source.SelsOk srcs osels base →
      (∀ s ∈ srcs, ∀ p ∈ s.fn.params, ∃ j < s.arity, p.2 = TyConsId.param j) →
      ∀ C ∈ (bindSourcesAux body rename vars rty base osels srcs).paramCons,
        ∃ k, P k ∧ C = TyConsId.param k
  | [], _, _, _, _, _, _, _ => by
      intro C hC
      exact absurd hC (by simp [FunTempl.paramCons, bindSourcesAux])
  | s :: srcs, vars, base, osels, hbase, hosels, hsel, hb => by
      intro C hC
      rw [Expr.bindSourcesAux_cons_paramCons, List.mem_append] at hC
      rcases hC with hC | hC
      · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hD
        obtain ⟨j, -, hpj⟩ := hb s List.mem_cons_self p hp
        rw [hpj, TyConsId.rename_param]
        refine ⟨_, ?_, rfl⟩
        rw [Source.ren]
        by_cases hmem : j ∈ s.fn.ty.params
        · rw [TyConsId.mergeRen_of_mem hmem]
          have hlt : s.fn.ty.params.idxOf j < (osels.headD []).length := by
            have h1 := List.idxOf_lt_length_iff.mpr hmem
            have h2 := hsel.2.1
            rw [Source.tyArity, TyConsId.arity] at h2
            omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
          cases osels with
          | nil => simp at hlt
          | cons o os => exact hosels o List.mem_cons_self _ (List.getElem_mem hlt)
        · rw [TyConsId.mergeRen_of_notMem hmem]
          exact hbase _ (Nat.le_add_right _ _)
      · exact mem_bindSourcesAux_paramCons_of P srcs vars.tail _ osels.tail
          (fun k hk => hbase k (Nat.le_trans (Nat.le_add_right _ _) hk))
          (fun o ho => hosels o (List.mem_of_mem_tail ho)) hsel.2.2
          (fun s' hs' => hb s' (List.mem_cons_of_mem _ hs')) C hC

end RUXt
