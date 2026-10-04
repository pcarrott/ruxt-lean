import RUXt.Model.Witness
import RUXt.Semantics.Summary.Basic
import RUXt.Semantics.Summary.Source.Specialise

/-!
# The witness program of a refutation

The semantics of the witness program `Source.witness` of a source at a family of picks:

* a program *realises* a description at a value (`Realises`) when, from the empty heap, it
  reaches every state that description allows, producing that value;
* a picked summary takes no input value, having no type parameter
  (`TypePicks.valArity_eq_zero`), and its source has no parameter
  (`TypePicks.params_eq_nil`);
* the body of the source of a pick realises the description the pick gives
  (`TypePicks.body_realises`) and is a well-typed program of the picked type
  (`TypePicks.body_safeProgram`);
* the resources the input values of a source are required to own, when its type parameters
  are described by a family of picks, are read off the descriptions of the picks, by rank
  (`Summary.pre_subvArgs`);
* the sources of the picked summaries bound by a step run, from the empty heap, into the states
  their descriptions allow (`TypePicks.runs_picks`);
* every specialisation step therefore typechecks and reproduces the behaviour of the source it
  specialises (`TypePicks.specStep_typechecks`, `TypePicks.specStep_frameStep`), both read off
  the corresponding halves of the correctness of specialisation
  (`Source.specialise_typechecks`, `Source.specialise_frameStep`), and so does the whole fold
  (`TypePicks.specFoldFn_spec`, `TypePicks.specFoldFn_frameStep`);
* the fully specialised source has no type parameter (`TypePicks.specialiseTypes_arity_self`),
  so the witness — its instantiation at the empty list of type arguments — is its
  concretisation at any tuple of type arguments, in particular at the picked types
  (`Source.witness_eq`);
* the witness thus reproduces the behaviour of the body on the input values
  (`Summary.witness_frameStep`) and is a well-typed main program
  (`Summary.witness_safeMain`).
-/

namespace RUXt

open scoped PFun

/-! ## Programs realising a description -/

/-- A program *realises* a description at a value: from the empty heap it reaches every
state the description allows of that value, producing it. -/
def Realises (Λ : Library) (e : Expr) (P : Val → Asrt.{0}) (v : Val) : Prop :=
  ∀ h, HProp h (P v) → Λ ⊢ ⟨∅ | e⟩ ⇓ᵢ ⟨h | .ok v⟩

/-! ## The programs of the picks

A family of picks available in a valid type space (`TypePicks.Safe`) picks, for every type
parameter of the source, valid summaries without type parameter filed for the type constructor
of a concrete type (`TypePicks.IsPick`).  Such a summary takes no input value either: every
parameter of a valid source carries one of its type parameters, and it has none
(`TypePicks.valArity_eq_zero`). -/

namespace TypePicks

/-- The types a family of picks supplies for `n` type parameters. -/
def tys (P : TypePicks) (n : ℕ) : TyArgs n :=
  TyArgs.ofListPad n (P.map (·.1))

/-- The family of picks describing every type parameter of the source `s` by the unit type and
the summary of unit values, once per parameter carrying it. -/
def unit (s : Source) : TypePicks :=
  (List.range s.arity).map fun i =>
    (Ty.unit, List.replicate (s.paramCount i) (Summary.base .unit))

/-- A summary may be picked for the concrete type `τ` in the type space `S`: it is filed there
for the type constructor of `τ`, and has no type parameter. -/
def IsPick (S : SummCtx) (τ : Ty) (ς : Summary) : Prop :=
  S.MemTy τ.consId ς ∧ ς.src.arity = 0

/-- Every summary picked for the first `n` type parameters may be picked for the type picked
alongside it.  This is the part of `TypePicks.Safe` that does not depend on the source. -/
def Avail (P : TypePicks) (S : SummCtx) (n : ℕ) : Prop :=
  ∀ i < n, ∀ ς ∈ (P.pick i).2, IsPick S (P.pick i).1 ς

/-- A family of picks available for a source picks summaries that may be picked. -/
theorem Safe.avail {P : TypePicks} {S : SummCtx} {s : Source} (hP : P.Safe S s) :
    P.Avail S s.arity :=
  fun i hi => (hP.2 i hi).2

/-- A family of picks available for a source picks one summary per parameter carrying each
type parameter. -/
theorem Safe.length_eq {P : TypePicks} {S : SummCtx} {s : Source} (hP : P.Safe S s) :
    ∀ i < s.arity, (P.pick i).2.length = (s.specParams i).length :=
  fun i hi => (hP.2 i hi).1.trans Source.length_specParams.symm

variable {Λ : Library} {S : SummCtx} {τ : Ty} {ς : Summary}

/-- A picked summary is valid, at the type constructor of the type it is picked for. -/
theorem valid (hctx : S.Valid Λ) (hς : IsPick S τ ς) : ς.Valid Λ τ.consId :=
  hctx _ _ hς.1

/-- The source of a picked summary has no parameter: it has no type parameter, and every
parameter of a valid source carries one of its type parameters. -/
theorem params_eq_nil (hctx : S.Valid Λ) (hς : IsPick S τ ς) : ς.src.fn.params = [] := by
  obtain ⟨hparams, -⟩ := (valid hctx hς).typechecks.1
  refine List.eq_nil_iff_forall_not_mem.mpr fun q hq => ?_
  obtain ⟨j, hj, -⟩ := hparams q hq
  rw [hς.2] at hj
  exact Nat.not_lt_zero _ hj

/-- The source of a picked summary has no parameter name. -/
theorem paramNames_eq_nil (hctx : S.Valid Λ) (hς : IsPick S τ ς) : ς.src.fn.paramNames = [] :=
  FunTempl.paramNames_eq_nil (params_eq_nil hctx hς)

/-- **A picked summary takes no input value**: this need not be required of a pick, it follows
from its having no type parameter. -/
theorem valArity_eq_zero (hctx : S.Valid Λ) (hς : IsPick S τ ς) : ς.valArity = 0 := by
  rw [← (valid hctx hς).wellShaped, params_eq_nil hctx hς, List.length_nil]

/-- The input values a picked summary is run at: there are none. -/
theorem args_snd_toList_eq_nil (hctx : S.Valid Λ) (hς : IsPick S τ ς)
    (a : TeleArg ς.ownedTele) : a.snd.toList = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [TeleArg.toList_length]
  exact valArity_eq_zero hctx hς

/-- The source of a picked summary has a single tuple of type arguments: it has no type
parameter. -/
theorem tyArgs_eq (hς : IsPick S τ ς) (T T' : TyArgs ς.src.arity) : T = T' :=
  TyArgs.ext fun _ hj => absurd hj (by rw [hς.2]; omega)

/-- **The program of a pick realises its description**: the body of the source of a picked
summary, at any symbolic values `a`, reaches from the empty heap every state the postcondition
of that summary at `a` describes of a value, producing that value. -/
theorem body_realises (hctx : S.Valid Λ) (hς : IsPick S τ ς)
    (a : TeleArg ς.src.teleOf) (T : TyArgs ς.src.arity) (v : Val) :
    Realises Λ ((ς.src.fn.body.apply a).apply T)
      (fun v => ς.ownedAt v (TeleArg.app a (TeleArg.replicate _ Val.unit))
        (SubvArgs.ofTys (TeleArg.replicate _ Ty.unit))) v := by
  intro h hh
  obtain ⟨hp₀, hpre, ε, hε, hstep⟩ :=
    (valid hctx hς).triple_apply (TeleArg.app a (TeleArg.replicate _ Val.unit))
      (SubvArgs.ofTys (TeleArg.replicate _ Ty.unit)) v h hh
  obtain rfl : ε = .ok v := Option.some.inj hε.symm
  have hnil := args_snd_toList_eq_nil hctx hς (TeleArg.app a (TeleArg.replicate _ Val.unit))
  obtain rfl : hp₀ = ∅ := by
    rwa [Summary.pre_apply_eq_emp _ _ _ _ hnil, hProp_emp] at hpre
  rw [Summary.expr_apply, paramNames_eq_nil hctx hς, Expr.substs_nil_left, TeleArg.fst_append,
    tyArgs_eq hς (SubvArgs.tys _) T] at hstep
  exact hstep

/-- The anonymous form of a constructor using no type parameter is that constructor. -/
private theorem anon_of_params_nil {c : TyConsId} (h : c.params = []) : c.anon = c := by
  rw [TyConsId.anon]
  refine Eq.trans (TyConsId.rename_congr (σ := fun i => i) c ?_) (TyConsId.rename_id c)
  intro i hi
  rw [h] at hi
  exact absurd hi (by simp)

/-- The source of a picked summary produces the type constructor of the type it is picked
for. -/
theorem src_ty_eq (hctx : S.Valid Λ) (hς : IsPick S τ ς) : ς.src.fn.ty = τ.consId := by
  have hmatch := (valid hctx hς).src_ty
  have hparams : ς.src.fn.ty.params = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [← TyConsId.arity, hmatch.arity_eq, TyConsId.arity, TyConsId.params_consId]
    rfl
  rw [← anon_of_params_nil hparams, ← anon_of_params_nil (TyConsId.params_consId τ)]
  exact hmatch

/-- The result type of the source of a picked summary is the type it is picked for: it is filed
for the type constructor of that concrete type, which uses no type parameter. -/
theorem concretise_ty (hctx : S.Valid Λ) (hς : IsPick S τ ς)
    (a : TeleArg ς.src.teleOf) (T : TyArgs ς.src.arity) :
    (ς.src.fn.concretise a T).ty = τ := by
  rw [FunTempl.concretise, FunTempl.resTy_apply, src_ty_eq hctx hς, TyConsId.concretise_consId]

/-- The source of a picked summary has no parameter once concretised. -/
theorem concretise_params (hctx : S.Valid Λ) (hς : IsPick S τ ς)
    (a : TeleArg ς.src.teleOf) (T : TyArgs ς.src.arity) :
    (ς.src.fn.concretise a T).params = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [FunTempl.length_params_concretise, params_eq_nil hctx hς, List.length_nil]

/-- The program of a pick is a well-typed program of the picked type, in any context: the
source of the picked summary typechecks and takes no input value. -/
theorem body_safeProgram (hctx : S.Valid Λ) (hς : IsPick S τ ς)
    (a : TeleArg ς.src.teleOf) (T : TyArgs ς.src.arity) (𝕍 : VarCtx) :
    SafeProgram 𝕍 Λ τ ((ς.src.fn.body.apply a).apply T) := by
  obtain ⟨hsafe, -, -⟩ := (valid hctx hς).typechecks.concretise_typechecks a T
  rw [concretise_ty hctx hς a T] at hsafe
  refine safeProgram_subset hsafe ?_
  rw [FunImpl.paramNames, concretise_params hctx hς a T, List.map_nil, List.map_nil]
  exact PFun.empty_subset _

/-! ### The picks describing the unit type -/

/-- The unit picks for a source are available for it in every type space holding the summary
of unit values. -/
theorem unit_safe {s : Source} (h : S.MemTy (.base .unit) (Summary.base .unit)) :
    (TypePicks.unit s).Safe S s := by
  refine ⟨by simp [TypePicks.unit], fun i hi => ?_⟩
  have hpick : (TypePicks.unit s).pick i
      = (Ty.unit, List.replicate (s.paramCount i) (Summary.base .unit)) := by
    simp [TypePicks.pick, TypePicks.unit, List.getD_eq_getElem?_getD, hi]
  rw [hpick]
  exact ⟨List.length_replicate .., fun _ hς => by
    obtain rfl := List.eq_of_mem_replicate hς
    exact ⟨h, Summary.base_src_arity .unit⟩⟩

/-! ## The types and resources the picks describe -/

/-- The type a family of picks supplies for a type parameter is the type picked for it. -/
theorem get_tys (P : TypePicks) {n i : ℕ} (hi : i < n) : (P.tys n).get i = (P.pick i).1 := by
  rw [TyArgs.get, tys, TyArgs.ofListPad, TeleArg.ofListPad, TeleArg.toList_transport, TeleArg.toList_ofList, pick,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  rcases Nat.lt_or_ge i P.length with h | h
  · rw [List.getElem?_append_left (by simpa using h), List.getElem?_map]
    cases P[i]? <;> rfl
  · rw [List.getElem?_append_right (by simpa using h), List.getElem?_replicate,
      if_pos (by simp only [List.length_map]; omega), List.getElem?_eq_none h]
    rfl

/-- The first `n` of the picked types for `n + k` type parameters are the picked types for `n`
type parameters. -/
@[simp] theorem splitUniform_tys (P : TypePicks) (n k : ℕ) :
    ((P.tys (n + k)).splitUniform n k).1 = P.tys n :=
  TyArgs.ext fun _ hi => by
    rw [TyArgs.get_splitUniform_left _ hi, get_tys P (Nat.lt_add_right _ hi), get_tys P hi]

/-- The symbolic values of the summaries picked for the last of the first `k + 1` type
parameters are the first block of the tuple. -/
@[simp] theorem pickArgs_last (P : TypePicks) {k : ℕ} (a : TeleArg (P.mergedTele (k + 1))) :
    P.pickArgs a (Fin.last k) = a.fst :=
  Fin.lastCases_last (motive := fun i => TeleArg (P.pickTele i))

/-- The symbolic values of the summaries picked for one of the first `k` type parameters are
read off the rest of the tuple. -/
@[simp] theorem pickArgs_castSucc (P : TypePicks) {k : ℕ} (a : TeleArg (P.mergedTele (k + 1)))
    (j : Fin k) : P.pickArgs a j.castSucc = P.pickArgs a.snd j :=
  Fin.lastCases_castSucc (motive := fun i => TeleArg (P.pickTele i)) j

/-- The description a family of picks supplies for a type parameter. -/
theorem get_subvArgs (P : TypePicks) {n i : ℕ} (a : TeleArg (P.mergedTele n))
    (hi : i < n) :
    (subvArgs P n a).get i = ⟨(P.pick i).1, posts (P.pick i).2 (P.pickArgs a ⟨i, hi⟩)⟩ := by
  rw [SubvArgs.get, subvArgs, TeleArg.toList_ofListPad _ (by simp),
    List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by rwa [List.length_finRange]), List.getElem_finRange]
  rfl

/-- The type a family of picks describes a type parameter at is the type picked for it. -/
theorem get_tys_subvArgs (P : TypePicks) {n i : ℕ} (a : TeleArg (P.mergedTele n))
    (hi : i < n) : (subvArgs P n a).tys.get i = (P.pick i).1 := by
  rw [SubvArgs.get_tys, get_subvArgs P a hi]

/-- **The types of the descriptions a family of picks supplies are the picked types**: the
types `TypePicks.tys` reads directly off the picks are the ones the descriptions
`TypePicks.subvArgs` are built at. -/
theorem tys_subvArgs (P : TypePicks) (n : ℕ) (a : TeleArg (P.mergedTele n)) :
    (subvArgs P n a).tys = P.tys n :=
  TyArgs.ext fun _ hi => by rw [get_tys_subvArgs P a hi, get_tys P hi]

/-- The index of the type parameter a bare type parameter constructor stands for; any other
constructor is sent to `0` (only bare type parameters are ever read through it). -/
def paramIdx : TyConsId → TyIdx
  | .param i => i
  | _ => 0

/-- The resources a value is required to own at a parameter carrying the type constructor `C`,
at rank `r`, when the type parameters are described by `D`: the `r`-th description `D` gives to
the type parameter `C` stands for, at the type picked for it. -/
def owns (Λ : Library) (P : TypePicks) (D : TyIdx → List (Val → Asrt.{0})) :
    TyConsId → ℕ → Val → Asrt.{0} :=
  fun C r v => (⟨(P.pick (paramIdx C)).1, D (paramIdx C)⟩ : TypedSubvariants).get Λ r v

end TypePicks

/-- **The resources the input values of a summary are required to own**, when its type
parameters are described by a family of picks at the symbolic values `a` of the picked
summaries: at every parameter, the value supplied there owns the description of the type
parameter that parameter carries of its rank. -/
theorem Summary.pre_subvArgs {Λ : Library} {ς : Summary} {P : TypePicks}
    (a : TeleArg (P.mergedTele ς.src.arity)) (hvalid : ς.src.fn.Valid)
    (args : TeleArg ς.ownedTele) :
    ς.pre Λ args (TypePicks.subvArgs P ς.src.arity a)
      = FunTempl.ownValsAt (TypePicks.owns Λ P fun j =>
          if h : j < ς.src.arity then TypePicks.posts (P.pick j).2 (P.pickArgs a ⟨j, h⟩) else [])
          (fun _ => 0)
          ς.src.fn.paramCons args.snd.toList := by
  rw [Summary.pre_apply]
  refine FunTempl.ownValsAt_congr _ _ _ fun C hC r v => ?_
  rw [FunTempl.paramCons, List.mem_map] at hC
  obtain ⟨q, hq, rfl⟩ := hC
  obtain ⟨j, hj, hqj⟩ := hvalid.1 q hq
  rw [hqj, TyConsId.ownsAt, TypePicks.get_subvArgs P a hj, TypePicks.owns, TypePicks.paramIdx,
    dif_pos hj]

/-! ## The sources the picks bind

The sources of picked summaries take no input value, have no type parameter and satisfy
`Source.Ok`; each of them reaches, from the empty heap, the state the description it gives
allows (`TypePicks.runs_picks`). -/

namespace TypePicks

variable {Λ : Library} {S : SummCtx} {τ : Ty} {ς : Summary}

/-- **The source of a pick satisfies `Source.Ok`**: it typechecks and has no parameter. -/
theorem src_ok (hctx : S.Valid Λ) (hς : IsPick S τ ς) : ς.src.Ok Λ :=
  ⟨(valid hctx hς).typechecks, by rw [paramNames_eq_nil hctx hς]; exact List.nodup_nil⟩

/-- A source without type parameter has no free type parameter. -/
theorem freeArity_eq_zero {s : Source} (h : s.arity = 0) : s.freeArity = 0 := by
  obtain ⟨tt, a, fn⟩ := s
  subst h
  rfl

/-- The sources of picked summaries take no input value. -/
theorem mergedValArity_picks (hctx : S.Valid Λ) :
    ∀ (ςs : List Summary), (∀ ς ∈ ςs, IsPick S τ ς) →
      Source.mergedValArity (ςs.map (·.src)) = 0
  | [], _ => rfl
  | ς :: ςs, h => by
    show ς.src.fn.params.length + Source.mergedValArity (ςs.map (·.src)) = 0
    rw [params_eq_nil hctx (h ς List.mem_cons_self),
      mergedValArity_picks hctx ςs fun ς' h' => h ς' (List.mem_cons_of_mem _ h')]
    rfl

/-- The sources of picked summaries have no type parameter. -/
theorem mergedFreeArity_picks :
    ∀ (ςs : List Summary), (∀ ς ∈ ςs, IsPick S τ ς) →
      Source.mergedFreeArity (ςs.map (·.src)) = 0
  | [], _ => rfl
  | ς :: ςs, h => by
    show ς.src.freeArity + Source.mergedFreeArity (ςs.map (·.src)) = 0
    rw [freeArity_eq_zero (h ς List.mem_cons_self).2,
      mergedFreeArity_picks ςs fun ς' h' => h ς' (List.mem_cons_of_mem _ h')]

/-- A list of summaries gives one description per summary. -/
@[simp] theorem length_posts :
    ∀ (ςs : List Summary) (a : TeleArg (Source.mergedTeleOf (ςs.map (·.src)))),
      (posts ςs a).length = ςs.length
  | [], _ => rfl
  | _ :: ςs, a => by
    show (posts ςs a.snd).length + 1 = ςs.length + 1
    rw [length_posts ςs a.snd]

/-- **The sources of the picked summaries run into the states their descriptions allow**: each
of them reaches, from the empty heap, the piece of the heap the postcondition of its summary at
its own symbolic values allows of the value supplied at the parameter it is bound at, and those
pieces are disjoint. -/
theorem runs_picks (hctx : S.Valid Λ)
    {own : TyConsId → ℕ → Val → Asrt.{0}} {N : ℕ} {types : TyArgs N} :
    ∀ (ςs : List Summary), (∀ ς ∈ ςs, IsPick S τ ς) →
      ∀ (a : TeleArg (Source.mergedTeleOf (ςs.map (·.src))))
      (off : TyConsId → ℕ) (osels : List (List TyIdx)) (base : ℕ)
      (values : TeleArg (Tele.uniform Val (Source.mergedValArity (ςs.map (·.src)))))
      (rs : List Val) (h : Heap),
      rs.length = ςs.length →
      HProp h (.iter (rs.zip (posts ςs a)) fun q => q.2 q.1) →
      Source.Runs Λ own types (ςs.map (·.src)) off osels base a values rs ∅ h := by
  intro ςs
  induction ςs with
  | nil =>
    intro _ a off osels base values rs h hlen hh
    obtain rfl : rs = [] := List.eq_nil_of_length_eq_zero hlen
    exact ⟨rfl, rfl, hProp_emp.mp hh⟩
  | cons ς ςs ih =>
    intro hςs a off osels base values rs h hlen hh
    have hς := hςs ς List.mem_cons_self
    cases rs with
    | nil => simp at hlen
    | cons v rs =>
      rw [show posts (ς :: ςs) a = _ :: posts ςs a.snd from rfl, List.zip_cons_cons,
        Asrt.iter_cons] at hh
      obtain ⟨h₁, h₂, rfl, hdisj, hh₁, hh₂⟩ := hh
      have hren : ς.src.renCons (osels.headD []) base = [] := by
        rw [Source.renCons, FunTempl.paramCons, params_eq_nil hctx hς]
        rfl
      refine ⟨v, rs, ∅, ∅, h₁, h₂, rfl, (PFun.empty_union ∅).symm, rfl, hdisj, ?own, ?step,
        ?rest⟩
      case own =>
        rw [hren]
        simp [FunTempl.ownValsAt, TyConsId.ranksFrom]
      case step =>
        rw [paramNames_eq_nil hctx hς, Expr.substs_nil_left]
        exact body_realises hctx hς _ _ v h₁ hh₁
      case rest =>
        exact ih (fun ς' h' => hςs ς' (List.mem_cons_of_mem _ h')) a.snd _ _ _ _ rs h₂
          (by simpa using hlen) hh₂

/-- The resources a list of values owns at repeated occurrences of one type constructor, read through a
reading giving, from the rank `off C` on, the descriptions of a list `L`: each value owns the
description of its own position. -/
theorem ownValsAt_replicate {Λ : Library} {own : TyConsId → ℕ → Val → Asrt.{0}} {C : TyConsId}
    {τ : Ty} :
    ∀ (L : List (Val → Asrt.{0})) (off : TyConsId → ℕ) (rs : List Val),
      (∀ r v, own C (off C + r) v = (⟨τ, L⟩ : TypedSubvariants).get Λ r v) →
      rs.length = L.length →
      FunTempl.ownValsAt own off (List.replicate L.length C) rs
        = .iter (rs.zip L) fun q => q.2 q.1
  | [], off, rs, _, hlen => by
    rw [List.eq_nil_of_length_eq_zero hlen]
    rfl
  | _ :: _, _, [], _, hlen => by simp at hlen
  | x :: L, off, v :: rs, hown, hlen => by
    rw [List.length_cons, List.replicate_succ, FunTempl.ownValsAt_cons,
      ownValsAt_replicate L (TyConsId.bumpOff off C) rs (fun r v => by
        rw [TyConsId.bumpOff, if_pos rfl, Nat.add_assoc, Nat.add_comm 1 r, hown (r + 1) v]; rfl)
        (by simpa using hlen),
      List.zip_cons_cons, Asrt.iter_cons, ← Nat.add_zero (off C), hown 0 v]
    rfl

end TypePicks

/-! ### The fully specialised source has no type parameter

Every step removes the type parameter it pins and adds none: the pinned constructor is that of a
concrete type, whose constructor uses no type parameter (`TyConsId.params_consId`), and the
sources bound for it have no type parameter. -/

namespace TypePicks

variable {S : SummCtx} {P : TypePicks} {m : ℕ}

/-- The fold of the specialisation steps is the plain fold `Nat.foldRev` of them, the last type
parameter first. -/
theorem specFoldFn_eq_foldRev (k : ℕ) (s : Source) :
    Source.mk _ _ (P.specFoldFn m k s).2 = Nat.foldRev k (fun i _ => P.specStep m i) s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih (P.specStep m k s)

/-- **The source specialised at all of its type parameters is the fold of the specialisation
steps** over them, the last type parameter first. -/
theorem specialiseTypes_eq_foldRev (s : Source) :
    s.specialiseTypes P =
      Nat.foldRev s.arity (fun i _ => P.specStep (maxNameLen s.fn.paramNames) i) s :=
  specFoldFn_eq_foldRev _ _

/-- A step removes the type parameter it pins, and adds none: the pinned constructor is that of
a concrete type, and the sources bound for it have no type parameter. -/
theorem specStep_arity {k : ℕ} (hP : P.Avail S (k + 1)) (s : Source) :
    (P.specStep m k s).arity = s.arity - 1 := by
  show s.arity - 1 + (P.pick k).1.consId.arity
    + Source.mergedFreeArity ((P.pick k).2.map (·.src)) = _
  rw [mergedFreeArity_picks _ (hP k (Nat.lt_succ_self k)), TyConsId.arity,
    TyConsId.params_consId]
  rfl

/-- Specialising the first `k` type parameters removes `k` type parameters. -/
theorem specFoldFn_arity :
    ∀ (k : ℕ) (s : Source), P.Avail S k →
      (P.specFoldFn m k s).1 = s.arity - k
  | 0, _, _ => rfl
  | k + 1, s, hP => by
    show (P.specFoldFn m k (P.specStep m k s)).1 = _
    rw [specFoldFn_arity k _ (fun i hi => hP i (by omega)), specStep_arity hP]
    omega

/-- **A source specialised at all of its type parameters has type arity `0`.** -/
theorem specialiseTypes_arity_self (s : Source) (hP : P.Safe S s) :
    (s.specialiseTypes P).arity = 0 := by
  show (P.specFoldFn _ s.arity s).1 = 0
  rw [specFoldFn_arity _ _ hP.avail]
  exact Nat.sub_self _

end TypePicks

/-! ## The specialisations the witness is built by

Each step of `Source.specialiseTypes` is an instance of `Source.specialise`, so it typechecks
and reproduces the behaviour of the source it specialises (`TypePicks.specStep_typechecks`,
`TypePicks.specStep_frameStep`); so does the whole fold (`TypePicks.specFoldFn_spec`,
`TypePicks.specFoldFn_frameStep`). -/

/-- Input values supplied at a list of parameters, taken apart into those supplied at the
parameters carrying the type parameter `i` and the others, together with the resources they
own, described by a list `rk` annotating the type constructors of the parameters: the values are
woven back from those two groups (`Source.weaveVals`). -/
theorem Source.exists_weaveVals_split {β : Type} (i : TyIdx) (f : Val → TyConsId × β → Asrt.{0}) :
    ∀ (ps : List (PVar × TyConsId)) (rk : List (TyConsId × β)) (vals : List Val) (h : Heap),
      rk.map Prod.fst = ps.map Prod.snd → vals.length = ps.length →
      HProp h (.iter (vals.zip rk) fun q => f q.1 q.2) →
      ∃ (rs vs : List Val) (h₁ h₂ : Heap), weaveVals i vs rs ps = vals ∧
        rs.length = (ps.filter fun p => p.2 == TyConsId.param i).length ∧
        vs.length = (ps.filter fun p => p.2 != TyConsId.param i).length ∧
        h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧
        HProp h₁ (.iter (rs.zip (rk.filter fun q => q.1 == TyConsId.param i))
          fun q => f q.1 q.2) ∧
        HProp h₂ (.iter (vs.zip (rk.filter fun q => q.1 != TyConsId.param i))
          fun q => f q.1 q.2) := by
  intro ps
  induction ps with
  | nil =>
    intro rk vals h hrk hlen hh
    obtain rfl : rk = [] := List.map_eq_nil_iff.mp hrk
    obtain rfl : vals = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    obtain rfl : h = ∅ := hh
    exact ⟨[], [], ∅, ∅, rfl, rfl, rfl, (PFun.empty_union ∅).symm, PFun.disjoint_empty_left _,
      hProp_emp.mpr rfl, hProp_emp.mpr rfl⟩
  | cons p ps ih =>
    intro rk vals h hrk hlen hh
    cases rk with
    | nil => simp at hrk
    | cons q rk =>
    rw [List.map_cons, List.map_cons, List.cons.injEq] at hrk
    obtain ⟨hq, hrk⟩ := hrk
    cases vals with
    | nil => simp at hlen
    | cons v vals =>
      rw [List.zip_cons_cons, Asrt.iter_cons] at hh
      obtain ⟨h₁, h₂, rfl, hdisj, hh₁, hh₂⟩ := hh
      obtain ⟨rs, vs, h₃, h₄, hw, hrs, hvs, rfl, hdisj34, hh₃, hh₄⟩ :=
        ih rk vals h₂ hrk (by simpa using hlen) hh₂
      rw [PFun.disjoint_union_right] at hdisj
      by_cases hp : p.2 = TyConsId.param i
      · have hpos : (p.2 == TyConsId.param i) = true := beq_iff_eq.mpr hp
        have hneg : ¬ ((p.2 != TyConsId.param i) = true) := by simp [hp]
        have hqpos : (q.1 == TyConsId.param i) = true := beq_iff_eq.mpr (hq.trans hp)
        have hqneg : ¬ ((q.1 != TyConsId.param i) = true) := by simp [hq, hp]
        refine ⟨v :: rs, vs, h₁ ∪ h₃, h₄, ?_, ?_, ?_, (PFun.union_assoc ..).symm,
          PFun.disjoint_union_left.mpr ⟨hdisj.2, hdisj34⟩, ?_, ?_⟩
        · rw [weaveVals_cons_pos ps vs _ hp, List.headD_cons, List.tail_cons, hw]
        · rw [@List.filter_cons_of_pos _ (fun q => q.2 == TyConsId.param i) p ps hpos,
            List.length_cons, List.length_cons, hrs]
        · rw [@List.filter_cons_of_neg _ (fun q => q.2 != TyConsId.param i) p ps hneg, hvs]
        · rw [@List.filter_cons_of_pos _ (fun q => q.1 == TyConsId.param i) q rk hqpos,
            List.zip_cons_cons, Asrt.iter_cons]
          exact ⟨h₁, h₃, rfl, hdisj.1, hh₁, hh₃⟩
        · rw [@List.filter_cons_of_neg _ (fun q => q.1 != TyConsId.param i) q rk hqneg]
          exact hh₄
      · have hpos : ¬ ((p.2 == TyConsId.param i) = true) := by simpa using hp
        have hneg : (p.2 != TyConsId.param i) = true := by simpa using hp
        have hqpos : ¬ ((q.1 == TyConsId.param i) = true) := by simpa [hq] using hp
        have hqneg : (q.1 != TyConsId.param i) = true := by simpa [hq] using hp
        refine ⟨rs, v :: vs, h₃, h₁ ∪ h₄, ?_, ?_, ?_, ?_,
          PFun.disjoint_union_right.mpr ⟨hdisj.1.symm, hdisj34⟩, ?_, ?_⟩
        · rw [weaveVals_cons_neg ps _ rs hp, List.headD_cons, List.tail_cons, hw]
        · rw [@List.filter_cons_of_neg _ (fun q => q.2 == TyConsId.param i) p ps hpos, hrs]
        · rw [@List.filter_cons_of_pos _ (fun q => q.2 != TyConsId.param i) p ps hneg,
            List.length_cons, List.length_cons, hvs]
        · rw [← PFun.union_assoc, PFun.union_comm hdisj.1, PFun.union_assoc]
        · rw [@List.filter_cons_of_neg _ (fun q => q.1 == TyConsId.param i) q rk hqpos]
          exact hh₃
        · rw [@List.filter_cons_of_pos _ (fun q => q.1 != TyConsId.param i) q rk hqneg,
            List.zip_cons_cons, Asrt.iter_cons]
          exact ⟨h₁, h₄, rfl, hdisj.2, hh₁, hh₄⟩

namespace TyConsId

/-- **Ranking commutes with filtering by constructor**: the rank of a constructor only counts
the occurrences of that very constructor before it, and a filter on constructors keeps either
all of them or none. -/
theorem ranksFrom_filter (p : TyConsId → Bool) : ∀ (cs : List TyConsId) (off : TyConsId → ℕ),
    (ranksFrom off cs).filter (fun q => p q.1) = ranksFrom off (cs.filter p)
  | [], _ => rfl
  | C :: cs, off => by
    by_cases hC : p C = true
    · rw [ranksFrom, List.filter_cons_of_pos (by simpa using hC), List.filter_cons_of_pos hC,
        ranksFrom, ranksFrom_filter p cs]
    · rw [ranksFrom, List.filter_cons_of_neg (by simpa using hC), List.filter_cons_of_neg hC,
        ranksFrom_filter p cs]
      refine ranksFrom_congr _ fun D hD => ?_
      have hD' : D ≠ C := fun h => hC (h ▸ (List.mem_filter.mp hD).2)
      rw [bumpOff, if_neg hD']

end TyConsId

/-- Input values supplied at a list of parameters owning what a ranked reading of their
constructors describes, taken apart into those supplied at the parameters carrying the type
parameter `i` and the others: each group owns what the same reading describes at its own
parameters, the ranks being unchanged. -/
theorem Source.exists_weaveVals_split_ranked (i : TyIdx) (own : TyConsId → ℕ → Val → Asrt.{0})
    (ps : List (PVar × TyConsId)) (vals : List Val) (h : Heap) (hlen : vals.length = ps.length)
    (hh : HProp h (FunTempl.ownValsAt own (fun _ => 0) (ps.map Prod.snd) vals)) :
    ∃ (rs vs : List Val) (h₁ h₂ : Heap), weaveVals i vs rs ps = vals ∧
      rs.length = (ps.filter fun p => p.2 == TyConsId.param i).length ∧
      vs.length = (ps.filter fun p => p.2 != TyConsId.param i).length ∧
      h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧
      HProp h₁ (FunTempl.ownValsAt own (fun _ => 0)
        ((ps.filter fun p => p.2 == TyConsId.param i).map Prod.snd) rs) ∧
      HProp h₂ (FunTempl.ownValsAt own (fun _ => 0)
        ((ps.filter fun p => p.2 != TyConsId.param i).map Prod.snd) vs) := by
  obtain ⟨rs, vs, h₁, h₂, hw, hrs, hvs, hh12, hdisj, hh₁, hh₂⟩ :=
    Source.exists_weaveVals_split i (fun v q => own q.1 q.2 v) ps
      (TyConsId.ranksFrom (fun _ => 0) (ps.map Prod.snd)) vals h
      (TyConsId.map_fst_ranksFrom _ _) hlen hh
  refine ⟨rs, vs, h₁, h₂, hw, hrs, hvs, hh12, hdisj, ?_, ?_⟩
  · have e := TyConsId.ranksFrom_filter (fun C => C == TyConsId.param i) (ps.map Prod.snd)
      (fun _ => 0)
    rw [e] at hh₁
    have e2 : (ps.filter fun p => p.2 == TyConsId.param i).map Prod.snd
        = (ps.map Prod.snd).filter (fun C => C == TyConsId.param i) := by
      rw [List.filter_map]
      rfl
    rw [FunTempl.ownValsAt, e2]
    exact hh₁
  · have e := TyConsId.ranksFrom_filter (fun C => C != TyConsId.param i) (ps.map Prod.snd)
      (fun _ => 0)
    rw [e] at hh₂
    have e2 : (ps.filter fun p => p.2 != TyConsId.param i).map Prod.snd
        = (ps.map Prod.snd).filter (fun C => C != TyConsId.param i) := by
      rw [List.filter_map]
      rfl
    rw [FunTempl.ownValsAt, e2]
    exact hh₂

namespace TypePicks

variable {Λ : Library} {S : SummCtx} {P : TypePicks} {m : ℕ}

/-! ### One specialisation step -/

section Step

variable {k : ℕ} {s : Source}

/-- The sources a step binds are those of the summaries picked for the type parameter it pins,
and they produce the constructor it pins that parameter to. -/
theorem specStep_srcs_match (hctx : S.Valid Λ) (hP : P.Avail S (k + 1)) {s' : Source}
    (hs' : s' ∈ (P.pick k).2.map (·.src)) :
    s'.fn.ty.Match (P.pick k).1.consId := by
  obtain ⟨ς, hς, rfl⟩ := List.mem_map.mp hs'
  rw [src_ty_eq hctx (hP k (Nat.lt_succ_self k) ς hς)]

/-- The constructor of a concrete type is in anonymous form: it uses no type parameter. -/
theorem consId_anon (τ : Ty) : τ.consId.anon = τ.consId :=
  anon_of_params_nil (TyConsId.params_consId τ)

/-- The sources a step binds name their type parameters in the order of the anonymous form of
the constructor they produce: that constructor uses no type parameter. -/
theorem specStep_srcs_inAnonOrder (hctx : S.Valid Λ) (hP : P.Avail S (k + 1)) {s' : Source}
    (hs' : s' ∈ (P.pick k).2.map (·.src)) : s'.fn.ty.InAnonOrder := by
  obtain ⟨ς, hς, rfl⟩ := List.mem_map.mp hs'
  rw [src_ty_eq hctx (hP k (Nat.lt_succ_self k) ς hς), TyConsId.InAnonOrder, TyConsId.arity,
    TyConsId.params_consId]
  rfl

/-- The sources a step binds are acceptable to the specialisation. -/
theorem specStep_srcs_ok (hctx : S.Valid Λ) (hP : P.Avail S (k + 1)) :
    ∀ s' ∈ (P.pick k).2.map (·.src), s'.Ok Λ := by
  intro s' hs'
  obtain ⟨ς, hς, rfl⟩ := List.mem_map.mp hs'
  exact src_ok hctx (hP k (Nat.lt_succ_self k) ς hς)

/-- The sources a step binds have no parameter name. -/
theorem specStep_srcs_paramNames (hctx : S.Valid Λ) (hP : P.Avail S (k + 1)) :
    ∀ s' ∈ (P.pick k).2.map (·.src), ∀ y ∈ s'.fn.paramNames, y.length ≤ m := by
  intro s' hs'
  obtain ⟨ς, hς, rfl⟩ := List.mem_map.mp hs'
  rw [paramNames_eq_nil hctx (hP k (Nat.lt_succ_self k) ς hς)]
  simp

/-- The parameters of a source specialised by a step at its last type parameter: the ones it
keeps, unchanged — the pinned parameters are let-bound, the bound sources take no input value,
and the type parameters the kept ones carry stay in place. -/
theorem specStep_params (hctx : S.Valid Λ) (hP : P.Avail S (k + 1)) (hvalid : s.fn.Valid)
    (harity : s.arity = k + 1) :
    (P.specStep m k s).fn.params = s.restParams k := by
  show (s.pinnedParams k (P.pick k).1.consId).2
      ++ boundParams m (List.replicate (P.pick k).2.length ((P.pick k).1.consId.shiftTo k)) (s.arity - 1 + (P.pick k).1.consId.arity)
        ((P.pick k).2.map (·.src)) = _
  have hnil : boundParams m (List.replicate (P.pick k).2.length ((P.pick k).1.consId.shiftTo k)) (s.arity - 1 + (P.pick k).1.consId.arity)
      ((P.pick k).2.map (·.src)) = [] :=
    List.eq_nil_of_length_eq_zero (by
      rw [Source.length_boundParams, mergedValArity_picks hctx _ (hP k (Nat.lt_succ_self k))])
  rw [Source.pinnedParams_snd, hnil, List.append_nil]
  refine (List.map_congr_left fun p hp => ?_).trans (List.map_id _)
  rw [Source.restParams, List.mem_filter] at hp
  obtain ⟨j, hj, hpj⟩ := hvalid.1 p hp.1
  have hne : ¬ j = k := fun h => by simp [hpj, h] at hp
  have hlt : j < k := by omega
  rw [hpj, TyConsId.substCons_param, TyConsId.specSubst, if_neg hne,
    if_pos hlt, TyConsId.keptIdx, if_pos hlt, ← hpj]
  rfl

/-- The parameter names a step keeps. -/
theorem specStep_paramNames (hctx : S.Valid Λ) (hP : P.Avail S (k + 1)) (hvalid : s.fn.Valid)
    (harity : s.arity = k + 1) :
    (P.specStep m k s).fn.paramNames = s.restVars k := by
  rw [FunTempl.paramNames, specStep_params hctx hP hvalid harity]
  rfl

/-- The parameters carrying another type parameter are unchanged by a step. -/
theorem specStep_specParams (hctx : S.Valid Λ) (hP : P.Avail S (k + 1)) (hvalid : s.fn.Valid)
    (harity : s.arity = k + 1) {j : TyIdx} (hj : j ≠ k) :
    (P.specStep m k s).specParams j = s.specParams j := by
  rw [Source.specParams, specStep_params hctx hP hvalid harity, Source.restParams,
    Source.specParams, List.filter_filter]
  refine List.filter_congr fun p _ => ?_
  by_cases h : p.2 = TyConsId.param j
  · simp [h, hj]
  · simp [h]

/-- The type arguments the source a step specialises is run at, when the specialised source is
run at the picked types: the picked types. -/
theorem specTyArgs_tys (harity : s.arity = k + 1) {M : ℕ} (hM : k ≤ M) :
    s.specTyArgs k (P.pick k).1.consId (P.tys M) = P.tys s.arity := by
  have hk : k < s.arity := by omega
  refine TyArgs.ext fun j hj => ?_
  rw [get_tys P hj, Source.specTyArgs_eq (consId_anon _) hk, TyArgs.get,
    TeleArg.getD_toList_insertUniformPred _ Ty.unit k hk _ j]
  by_cases hjk : j = k
  · rw [if_pos hjk, TyConsId.shiftTo_consId, TyConsId.concretise_consId, hjk]
  · have hlt : j < k := by omega
    have hj' : j < s.arity - 1 := by omega
    have hjM : j < M := by omega
    rw [if_neg hjk, if_pos hlt, ← TyArgs.get, TyArgs.get_reindex hj', TyConsId.keptIdx,
      if_pos hlt]
    exact get_tys P hjM

/-- **A specialisation step typechecks**, and keeps names bounded by `m`. -/
theorem specStep_typechecks (args : TeleArg s.teleOf) (hctx : S.Valid Λ)
    (hP : P.Avail S (k + 1)) (hlenk : (P.pick k).2.length = (s.specParams k).length)
    (htc : s.Typechecks Λ) (harity : s.arity = k + 1)
    (hlen : ∀ y ∈ s.fn.paramNames, y.length ≤ m) :
    (P.specStep m k s).Typechecks Λ :=
  Source.specialise_typechecks htc (harity ▸ Nat.lt_succ_self k) (consId_anon _)
    (specStep_srcs_ok hctx hP) (fun _ hs' => specStep_srcs_match hctx hP hs')
    (fun _ hs' => specStep_srcs_inAnonOrder hctx hP hs') hlen (specStep_srcs_paramNames hctx hP)
    (htc.paramNames_nodup args) ((List.length_map _).trans hlenk)

/-- The type a step produces, at the picked types, is the one the source it specialises
produces there. -/
theorem specStep_ty (htc : s.Typechecks Λ) (harity : s.arity = k + 1) :
    (P.specStep m k s).fn.ty.concretise (P.tys (P.specStep m k s).arity)
      = s.fn.ty.concretise (P.tys s.arity) := by
  show (s.fn.ty.substCons (TyConsId.specSubst k (P.pick k).1.consId)).concretise _ = _
  have hkM : k ≤ (P.specStep m k s).arity := by
    show k ≤ s.arity - 1 + _ + _
    omega
  rw [Source.specTyArgs_concretise (consId_anon _) htc.ty_bounded (harity ▸ Nat.lt_succ_self k),
    specTyArgs_tys (P := P) harity hkM]

/-- The type constructors of the parameters a step pins are all the type parameter it pins. -/
theorem map_snd_specParams :
    (s.specParams k).map Prod.snd = List.replicate (s.specParams k).length (.param k) := by
  refine List.eq_replicate_iff.mpr ⟨List.length_map _, fun C hC => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC
  simpa using (List.mem_filter.mp hp).2

/-- **The behaviour of a specialisation step**: a source run at the picked types on input
values owning what the descriptions `D` give is reproduced by the source a step specialises it
to, run on the input values it keeps — the sources bound at the pinned parameters producing, from
the empty heap, the values supplied there together with what they own.  The descriptions of the
pinned type parameter are those the summaries picked for it give at their symbolic values. -/
theorem specStep_frameStep (hctx : S.Valid Λ) (hP : P.Avail S (k + 1))
    (hlenk : (P.pick k).2.length = (s.specParams k).length)
    (htc : s.Typechecks Λ) (harity : s.arity = k + 1)
    (hlen : ∀ y ∈ s.fn.paramNames, y.length ≤ m)
    {D : TyIdx → List (Val → Asrt.{0})} (b : TeleArg (P.specStep m k s).teleOf)
    (hD : D k = posts (P.pick k).2 b.snd)
    {vals : List Val} {hF hp h' : Heap} {ε : Exit}
    (hvals : vals.length = s.fn.params.length)
    (hpre : HProp hp (FunTempl.ownValsAt (owns Λ P D) (fun _ => 0) s.fn.paramCons vals))
    (hdisj : hF ##ₘ hp)
    (hstep : Λ ⊢ ⟨hF ∪ hp | ((s.fn.body.apply b.fst).apply (P.tys s.arity)).substs
      s.fn.paramNames (Term.ofVals vals)⟩ ⇓ᵢ ⟨h' | ε⟩) :
    ∃ (vals' : List Val) (hp' : Heap),
      vals'.length = (P.specStep m k s).fn.params.length ∧
      HProp hp' (FunTempl.ownValsAt (owns Λ P D) (fun _ => 0) (P.specStep m k s).fn.paramCons
        vals') ∧
      hF ##ₘ hp' ∧
      Λ ⊢ ⟨hF ∪ hp' |
          (((P.specStep m k s).fn.body.apply b).apply
          (P.tys (P.specStep m k s).arity)).substs (P.specStep m k s).fn.paramNames
          (Term.ofVals vals')⟩ ⇓ᵢ ⟨h' | ε⟩ := by
  have hvalid : s.fn.Valid := htc.src_valid
  have hk : k < k + 1 := Nat.lt_succ_self k
  obtain ⟨rs, vs, h₁, h₂, hw, hrs, hvs, rfl, hdisj12, hh₁, hh₂⟩ :=
    Source.exists_weaveVals_split_ranked k (owns Λ P D) s.fn.params vals hp hvals hpre
  rw [PFun.disjoint_union_right] at hdisj
  have hparams := specStep_params (P := P) (m := m) hctx hP hvalid harity
  have hsrcs : ((P.pick k).2.map (·.src)).length = (s.specParams k).length :=
    (List.length_map _).trans hlenk
  refine ⟨vs, h₂, ?_, ?_, hdisj.2, ?_⟩
  · rw [hparams, hvs]
    rfl
  · rw [FunTempl.paramCons, hparams]
    exact hh₂
  · -- the values produced by the bound sources own the descriptions their summaries give
    have hcopies : HProp h₁ (.iter (rs.zip (posts (P.pick k).2 b.snd)) fun q => q.2 q.1) := by
      have hrep : (s.specParams k).map Prod.snd = List.replicate
          (posts (P.pick k).2 b.snd).length (.param k) := by
        rw [length_posts, hlenk]
        exact map_snd_specParams
      have e : (s.fn.params.filter fun p => p.2 == TyConsId.param k) = s.specParams k := rfl
      rw [e, hrep, ownValsAt_replicate (τ := (P.pick k).1) _ _ _ (fun r v => by
          show TypedSubvariants.get ⟨(P.pick k).1, D k⟩ Λ (0 + r) v = _
          rw [Nat.zero_add, hD]) (by rw [length_posts, hlenk, hrs]; rfl)] at hh₁
      exact hh₁
    obtain ⟨-, -, hrun⟩ :=
      Source.specialise_frameStep (m := m) (own := fun _ _ _ => Asrt.emp) (off := fun _ => 0)
        (τ := (P.pick k).1.consId) (harity ▸ hk) (htc.ok b.fst) (specStep_srcs_ok hctx hP)
        (fun _ hs' => specStep_srcs_match hctx hP hs')
        (fun _ hs' => specStep_srcs_inAnonOrder hctx hP hs')
        (Source.selsOk_specSels (harity ▸ hk) hsrcs fun _ hs' => specStep_srcs_match hctx hP hs')
        (specStep_srcs_paramNames hctx hP) hlen (htc.paramNames_nodup b.fst)
        hsrcs b.fst b.snd (P.tys _) (TeleArg.replicate _ Val.unit)
        vs rs ∅ (hF ∪ h₂) h₁ h' ε hvs
        (PFun.disjoint_union_left.mpr ⟨hdisj.1, hdisj12.symm⟩)
        (runs_picks hctx (P.pick k).2 (hP k hk) b.snd _ _ _ _ rs h₁
          (by rw [hrs, hlenk]; rfl) hcopies)
        (by
          rw [hw, specTyArgs_tys harity, PFun.union_assoc, PFun.union_comm hdisj12.symm]
          · exact hstep
          · show k ≤ s.arity - 1 + _ + _
            omega)
    have hnil : (TeleArg.replicate (Source.mergedValArity
        ((P.pick k).2.map (·.src))) Val.unit).toList = [] :=
      List.eq_nil_of_length_eq_zero
        (by rw [TeleArg.toList_length, mergedValArity_picks hctx _ (hP k hk)])
    rw [hnil, List.append_nil, PFun.union_empty, TeleArg.app_fst_snd] at hrun
    exact hrun

end Step

/-! ### The whole fold -/

/-- A source with no type parameter that typechecks has no parameter. -/
theorem params_eq_nil_of_arity_eq_zero {s : Source} (hvalid : s.fn.Valid)
    (harity : s.arity = 0) : s.fn.params = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun p hp => by
    obtain ⟨j, hj, -⟩ := hvalid.1 p hp
    omega

/-- The hypotheses of the fold, carried from a source to the source a step specialises it to:
the summaries picked for the type parameters still to be pinned fit the parameters carrying
them, and the parameter names stay bounded by `m`. -/
theorem specStep_fold_hyps {k : ℕ} {s : Source} (hctx : S.Valid Λ) (hP : P.Avail S (k + 1))
    (hlens : ∀ i < k + 1, (P.pick i).2.length = (s.specParams i).length)
    (htc : s.Typechecks Λ) (harity : s.arity = k + 1)
    (hlen : ∀ y ∈ s.fn.paramNames, y.length ≤ m) :
    (∀ i < k, (P.pick i).2.length = ((P.specStep m k s).specParams i).length) ∧
      (P.specStep m k s).arity = k ∧
      (∀ y ∈ (P.specStep m k s).fn.paramNames, y.length ≤ m) := by
  refine ⟨fun i hi => ?_, by rw [specStep_arity hP, harity]; rfl, ?_⟩
  · rw [specStep_specParams hctx hP htc.src_valid harity (Nat.ne_of_lt hi)]
    exact hlens i (by omega)
  · rw [specStep_paramNames hctx hP htc.src_valid harity]
    exact fun y hy => hlen y ((Source.restVars_sublist _ _).subset hy)

/-- **Specialising the first `k` type parameters of a source with `k` type parameters**: the
fully specialised source typechecks, has no parameter, and produces the type the source produces
at the picked types. -/
theorem specFoldFn_spec (hctx : S.Valid Λ) (k : ℕ) (s : Source)
    (a : TeleArg (s.teleOf.app (P.mergedTele k)))
    (hP : P.Avail S k) (hlens : ∀ i < k, (P.pick i).2.length = (s.specParams i).length)
    (htc : s.Typechecks Λ) (harity : s.arity = k)
    (hlen : ∀ y ∈ s.fn.paramNames, y.length ≤ m) :
    (Source.mk _ _ (P.specFoldFn m k s).2).Typechecks Λ ∧
      (Source.mk _ _ (P.specFoldFn m k s).2).fn.params = [] ∧
      (Source.mk _ _ (P.specFoldFn m k s).2).fn.ty.concretise
          (P.tys (Source.mk _ _ (P.specFoldFn m k s).2).arity)
        = s.fn.ty.concretise (P.tys s.arity) := by
  induction k generalizing s with
  | zero => exact ⟨htc, params_eq_nil_of_arity_eq_zero htc.src_valid harity, rfl⟩
  | succ k ih =>
    obtain ⟨hlens', harity', hlen'⟩ := specStep_fold_hyps hctx hP hlens htc harity hlen
    obtain ⟨htc', hparams', hty'⟩ := ih (P.specStep m k s)
      a.assoc (fun i hi => hP i (by omega))
      hlens'
      (specStep_typechecks a.fst hctx hP (hlens k (Nat.lt_succ_self k)) htc harity hlen)
      harity' hlen'
    exact ⟨htc', hparams', hty'.trans (specStep_ty htc harity)⟩

/-- **The behaviour of the fully specialised source**: a source with `k` type parameters, run at
the picked types, at its own symbolic values `a.fst`, on input values owning what the picks
describe at the symbolic values `a.snd` of the picked summaries (`TypePicks.pickArgs`), is
reproduced from the empty heap by the source obtained by specialising all of them, at the
regrouped symbolic values (`TypePicks.foldReindexArgs`) — by definition symbolic values of the
specialised source. -/
theorem specFoldFn_frameStep (hctx : S.Valid Λ) :
    ∀ (k : ℕ) (s : Source) (a : TeleArg (s.teleOf.app (P.mergedTele k)))
      (D : TyIdx → List (Val → Asrt.{0})),
      P.Avail S k → (∀ i < k, (P.pick i).2.length = (s.specParams i).length) → s.Typechecks Λ →
      s.arity = k → (∀ y ∈ s.fn.paramNames, y.length ≤ m) →
      (∀ j (hj : j < k), D j = posts (P.pick j).2 (P.pickArgs a.snd ⟨j, hj⟩)) →
      ∀ (vals : List Val) (hF hp h' : Heap) (ε : Exit),
      vals.length = s.fn.params.length →
      HProp hp (FunTempl.ownValsAt (owns Λ P D) (fun _ => 0) s.fn.paramCons vals) →
      hF ##ₘ hp →
      (Λ ⊢ ⟨hF ∪ hp | ((s.fn.body.apply a.fst).apply (P.tys s.arity)).substs
        s.fn.paramNames (Term.ofVals vals)⟩ ⇓ᵢ ⟨h' | ε⟩) →
      Λ ⊢ ⟨hF |
        ((Source.mk _ _ (P.specFoldFn m k s).2).fn.body.apply
          (P.foldReindexArgs k s.teleOf a)).apply
        (P.tys (Source.mk _ _ (P.specFoldFn m k s).2).arity)⟩ ⇓ᵢ ⟨h' | ε⟩ := by
  intro k
  induction k with
  | zero =>
    intro s a D _ _ htc harity _ _ vals hF hp h' ε hvals hpre _ hstep
    have hparams := params_eq_nil_of_arity_eq_zero htc.src_valid harity
    obtain rfl : vals = [] := List.eq_nil_of_length_eq_zero (by rw [hvals, hparams]; rfl)
    obtain rfl : hp = ∅ := by
      rw [FunTempl.paramCons, hparams] at hpre
      exact hpre
    rw [FunTempl.paramNames_eq_nil hparams, Expr.substs_nil_left, PFun.union_empty] at hstep
    exact hstep
  | succ k ih =>
    intro s a D hP hlens htc harity hlen hD vals hF hp h' ε hvals hpre hdisj hstep
    obtain ⟨hlens', harity', hlen'⟩ := specStep_fold_hyps hctx hP hlens htc harity hlen
    have hDk : D k = posts (P.pick k).2
        (a.fst.app a.snd.fst :
          TeleArg (P.specStep m k s).teleOf).snd := by
      rw [hD k (Nat.lt_succ_self k), TeleArg.snd_append]
      exact congrArg _ (P.pickArgs_last a.snd)
    obtain ⟨vals', hp', hvals', hpre', hdisj', hstep'⟩ :=
      specStep_frameStep hctx hP (hlens k (Nat.lt_succ_self k)) htc harity hlen
        (a.fst.app a.snd.fst) hDk hvals hpre hdisj
        (by rw [TeleArg.fst_append]; exact hstep)
    exact ih (P.specStep m k s)
      a.assoc D (fun i hi => hP i (by omega))
      hlens' (specStep_typechecks a.fst hctx hP (hlens k (Nat.lt_succ_self k)) htc harity hlen)
      harity' hlen'
      (fun j hj => by
        rw [hD j (by omega), TeleArg.assoc, TeleArg.snd_append]
        exact congrArg _ (P.pickArgs_castSucc a.snd ⟨j, hj⟩))
      vals' hF hp' h' ε hvals' hpre' hdisj' (by rw [TeleArg.assoc, TeleArg.fst_append]; exact hstep')

/-- **A source specialised at all of its type parameters** (`Source.specialiseTypes`)
typechecks, has no parameter, and produces the type the source produces at the picked types. -/
theorem specialiseTypes_spec (hctx : S.Valid Λ) (s : Source)
    (a : TeleArg (s.typedTele P)) (hP : P.Safe S s) (htc : s.Typechecks Λ) :
    (s.specialiseTypes P).Typechecks Λ ∧
      (s.specialiseTypes P).fn.params = [] ∧
      (s.specialiseTypes P).fn.ty.concretise (P.tys (s.specialiseTypes P).arity)
        = s.fn.ty.concretise (P.tys s.arity) :=
  specFoldFn_spec hctx s.arity s a hP.avail hP.length_eq htc rfl
    (fun _ hy => le_maxNameLen hy)

end TypePicks

/-! ## The witness of a summary at a family of picks -/

/-- **The witness program is the body of the fully specialised source, concretised at the
regrouped model and at any tuple of type arguments**: the fully specialised source has type
arity `0` (`TypePicks.specialiseTypes_arity_self`), so its instantiation at the empty list of type
arguments succeeds, with its concretisation at any tuple of (zero) type arguments
(`FunTempl.instantiate_nil`) — in particular at the picked types. -/
theorem Source.witness_eq {S : SummCtx} (s : Source) (P : TypePicks) (hP : P.Safe S s)
    (args : TeleArg (s.typedTele P))
    (types : TyArgs (s.specialiseTypes P).arity) :
    s.witness P args =
      ((s.specialiseTypes P).fn.concretise
        (s.reindexArgs P args) types).body := by
  unfold Source.witness
  dsimp only
  rw [FunTempl.instantiate_nil (TypePicks.specialiseTypes_arity_self s hP) _ types]

namespace Summary

variable {Λ : Library} {S : SummCtx} {ς : Summary} {P : TypePicks}

/-- **The witness of a summary at a family of picks runs the source of that summary on any
input values the picks describe**: from the empty heap, it reproduces the run of the source at
the symbolic values `args.fst`, its type parameters being described at the symbolic values
`args.snd` of the picked summaries (`TypePicks.subvArgs`), from a state in which the input values
`vs` own what the picks describe. -/
theorem witness_frameStep (hctx : S.Valid Λ) (hP : P.Safe S ς.src)
    (htc : ς.src.Typechecks Λ) (hshape : ς.WellShaped)
    {args : TeleArg (ς.src.typedTele P)}
    {vs : TeleArg (.uniform Val ς.valArity)}
    {hp h' : Heap} {ε : Exit}
    (hpre : HProp hp (ς.pre Λ (args.fst.app vs) (P.subvArgs ς.src.arity args.snd)))
    (hstep : Λ ⊢ ⟨hp | ς.expr (args.fst.app vs) (P.subvArgs ς.src.arity args.snd)⟩
      ⇓ᵢ ⟨h' | ε⟩) :
    Λ ⊢ ⟨∅ | ς.src.witness P args⟩ ⇓ᵢ ⟨h' | ε⟩ := by
  rw [Source.witness_eq _ _ hP _ (P.tys _)]
  rw [Summary.expr_apply, TypePicks.tys_subvArgs] at hstep
  rw [Summary.pre_subvArgs _ htc.src_valid] at hpre
  simp only [TeleArg.fst_append, TeleArg.snd_append] at hstep hpre
  exact TypePicks.specFoldFn_frameStep hctx ς.src.arity ς.src args _ hP.avail
    hP.length_eq htc rfl (fun y hy => le_maxNameLen hy) (fun _ hj => dif_pos hj) vs.toList ∅ hp h' ε
    (by rw [TeleArg.toList_length]; exact hshape.symm) hpre (PFun.disjoint_empty_left hp)
    (by rw [PFun.empty_union]; exact hstep)

/-- **The witness of a summary at a family of picks is a well-typed main program**, at the
result type of its source at the types of the picks: the fully specialised source typechecks
(`Source.specialise_typechecks`, at every step), it has no parameter left, and it produces the
type the source of the summary produces at the picked types. -/
theorem witness_safeMain (hctx : S.Valid Λ) (hP : P.Safe S ς.src)
    (htc : ς.src.Typechecks Λ)
    (args : TeleArg (ς.src.typedTele P)) :
    SafeMain Λ (ς.src.fn.concretise args.fst (P.tys ς.src.arity)).ty
      (ς.src.witness P args) := by
  obtain ⟨htc', hparams, hty⟩ :=
    TypePicks.specialiseTypes_spec hctx ς.src args hP htc
  set a' := ς.src.reindexArgs P args
  obtain ⟨hsafe, -, -⟩ := htc'.concretise_typechecks a' (P.tys _)
  have hnil : ((ς.src.specialiseTypes P).fn.concretise a' (P.tys _)).params = [] :=
    List.eq_nil_of_length_eq_zero (by rw [FunTempl.length_params_concretise, hparams]; rfl)
  rw [FunImpl.paramNames, hnil, FunTempl.concretise_ty, FunTempl.resTy_apply, hty] at hsafe
  rw [Source.witness_eq _ _ hP _ (P.tys _)]
  show SafeProgram ∅ Λ _ _
  rw [FunTempl.concretise_ty, FunTempl.resTy_apply]
  exact hsafe

end Summary

end RUXt
