import RUXt.Model.Refute
import RUXt.Semantics.Logic.Solver
import RUXt.Semantics.Logic.Basic
import RUXt.Semantics.Summary.Source.Basic
import RUXt.Semantics.Summary.Subvariant.Basic

/-!
# Validity of summaries and summary contexts

The semantics of a summary: the triple it claims (`Summary.triple`), over its symbolic
values and input values followed by one typed subvariant per type parameter; the reachability
of its postcondition (`Summary.Reachable`); validity of a summary (`Summary.Valid`) and of a
type space (`SummCtx.Valid`); and the validity of the base summaries.
-/

namespace RUXt

/-! ### Validity of summaries -/

namespace Summary

/-- The resources required of the input values of a summary source, at a tuple of typed
subvariant arguments: at a parameter carrying a type parameter of the source, the resources
the typed subvariant supplied for it describes; at any other parameter, the opaque resource of
the type its constructor produces (`TyConsId.ownsAt`). -/
def pre (ς : Summary) (Λ : Library) (args : TeleArg ς.ownedTele)
    (S : SubvArgs.{0} ς.src.arity) : Asrt.{0} :=
  ς.src.fn.ownVals (fun C => C.ownsAt Λ S) args.snd.toList
/-- The source body, instantiated at the types of the typed subvariant arguments and with
its formal input variables replaced by the corresponding values. -/
def expr (ς : Summary) (args : TeleArg ς.ownedTele) (S : SubvArgs.{0} ς.src.arity) : Expr :=
  (ς.src.fn.body args.fst S.tys).substs
    ς.src.fn.paramNames (Term.ofVals args.snd.toList)
/-- The postcondition of a summary, as the assertion component of a triple. -/
def post (ς : Summary) (r : Val) (args : TeleArg ς.ownedTele)
    (S : SubvArgs.{0} ς.src.arity) : Asrt.{0} :=
  ς.ownedAt r args S
/-- The triple a summary claims: parametric on the typed subvariants its type parameters are
instantiated with, it runs the source of the summary on its input values, from the resources
those values are required to own (`Summary.pre`) to the resources the postcondition
describes. -/
def triple (ς : Summary) (Λ : Library) (ε : LExit) :
    SymTriple.{0} (polyTele ς.src.arity ς.ownedTele) :=
  polyTriple (ς.pre Λ) ς.expr ε ς.post

/-- The state `[ε : ς.owned]` is reachable from a safe source of the type constructor
`τ`. -/
def Reachable (ς : Summary) (Λ : Library) (τ : TyConsId) (ε : LExit) : Prop :=
  ς.src.fn.ty.Match τ ∧
    ς.src.Typechecks Λ ∧ UXFrameTriple Λ (ς.triple Λ ε)
/-- Semantic interpretation of valid summaries: the postcondition is reachable, satisfiable,
and the source has one parameter per input value of the postcondition (`Summary.WellShaped`). -/
def Valid (ς : Summary) (Λ : Library) (τ : TyConsId) : Prop :=
  ς.Reachable Λ τ .lok ∧ ς.SatOwned ∧ ς.WellShaped

end Summary

/-! ### Validity of summary contexts -/

namespace SummCtx

/-- Semantic interpretation of valid summary contexts. -/
def Valid (Λ : Library) (S : SummCtx) : Prop :=
  ∀ τ ς, S.MemTy τ ς → ς.Valid Λ τ

end SummCtx

/-! ## Properties

### Summaries given by a function -/

@[simp] theorem Summary.src_of (src : Source) (fn) : (Summary.of src fn).src = src := rfl
@[simp] theorem Summary.valArity_of (src : Source) (fn) :
    (Summary.of src fn).valArity = src.fn.params.length := rfl
/-- The assertion of a summary built by `Summary.of`: its postcondition applied to the
result value and to both tuples of arguments. -/
@[simp] theorem Summary.ownedAt_of (src : Source) (fn) (r : Val)
    (args : TeleArg (Summary.of src fn).ownedTele)
    (S : SubvArgs.{0} src.arity) {h : Heap} :
    HProp h ((Summary.of src fn).ownedAt r args S) ↔ HProp h (PolyAsrt.at (fn r) args S) :=
  Iff.rfl

/-! ### Owning resources through typed subvariants -/

/-- Reading the resources of a value at a renamed type constructor is reading them at the
constructor itself, through the reindexed tuple of typed subvariants. -/
theorem TyConsId.ownsAt_rename {C : TyConsId} {n m : ℕ} (Λ : Library) (ρ : TyIdx → TyIdx)
    (S : SubvArgs.{0} m) (k : ℕ) (v : Val) (h : C.Bounded n) (hρ : ∀ i ∈ C.params, ρ i < m) :
    (C.rename ρ).ownsAt Λ S k v = C.ownsAt Λ (TeleArg.reindex default ρ n S) k v := by
  cases C with
  | base kind => rfl
  | param i =>
    rw [TyConsId.rename_param, TyConsId.ownsAt_param, TyConsId.ownsAt_param,
      SubvArgs.get_reindex (h i (by simp))]
  | custom name args =>
    have hρ' : ((TyConsId.custom name args).rename ρ).Bounded m := TyConsId.Bounded.rename hρ
    rw [TyConsId.rename_custom] at hρ' ⊢
    rw [TyConsId.ownsAt_custom _ _ Λ S k v hρ', TyConsId.ownsAt_custom _ _ Λ _ k v h,
      SubvArgs.tys_reindex, TyConsId.concretise_reindex _ ρ S.tys h, TyConsId.rename_custom]

/-- Transporting a tuple of typed subvariants along an equality of arities does not change
the resources it describes. -/
theorem TyConsId.ownsAt_transport {C : TyConsId} {n m : ℕ} (Λ : Library) (h : n = m)
    (S : SubvArgs.{0} n) (k : ℕ) (v : Val) :
    C.ownsAt Λ (SubvArgs.transport h S) k v = C.ownsAt Λ S k v := by
  subst h; rfl

/-- The resources the input values of a bounded template own through a reindexed tuple of
typed subvariants are the ones they own at the renamed type constructors of its parameters:
the two sides read the same typed subvariant at every parameter, one by reindexing the
tuple, the other by renaming the constructor. -/
theorem FunTempl.ownVals_reindex {tt : Tele} {arity n : ℕ} (φ : FunTempl tt arity)
    (Λ : Library) (ρ : TyIdx → TyIdx) (S : SubvArgs.{0} n) (values : List Val)
    (hb : φ.Bounded) (hρ : ∀ i < arity, ρ i < n) :
    φ.ownVals (fun C => C.ownsAt Λ (TeleArg.reindex default ρ arity S)) values
      = φ.ownVals (fun C => (C.rename ρ).ownsAt Λ S) values := by
  refine FunTempl.ownVals_congr values fun C hC k v => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC
  exact (TyConsId.ownsAt_rename Λ ρ S k v (hb.param hp) fun i hi => hρ i (hb.param hp i hi)).symm

/-- The ranks, in a merge whose ranking starts from the offsets `off`, of the parameters of a
source that carry its type parameter `i`; the parameters of the source carry the type
constructors `cs`, renamed into the merge along `ρ`. -/
def TyConsId.selRanks (ρ : TyIdx → TyIdx) : (TyConsId → ℕ) → List TyConsId → TyIdx → List ℕ
  | _, [], _ => []
  | off, C :: cs, i =>
      if C = .param i then
        off (C.rename ρ) :: selRanks ρ (TyConsId.bumpOff off (C.rename ρ)) cs i
      else selRanks ρ (TyConsId.bumpOff off (C.rename ρ)) cs i

/-- Reading the resources of the input values of a bound source: at a tuple `T` of its own and
at the ranks of the source itself, they are the resources of the merge at the renamed
constructors and at the ranks of the merge.

The hypothesis `hcoh` is the coherence of `T` with the ranking: the subvariant the source reads
at rank `k` of its type parameter `i` is the one the merge supplies at the rank its `k`-th
parameter carrying `i` has. -/
theorem FunTempl.ownValsAt_select {Λ : Library} {M n : ℕ} (S : SubvArgs.{0} M)
    (T : SubvArgs.{0} n) (ρ : TyIdx → TyIdx) :
    ∀ (cs : List TyConsId) (values : List Val) (off loff : TyConsId → ℕ),
      (∀ C ∈ cs, ∃ i, C = .param i) →
      (∀ i, TyConsId.param i ∈ cs → ∀ k g, (TyConsId.selRanks ρ off cs i)[k]? = some g →
        ∀ v, (T.get i).get Λ (loff (.param i) + k) v = (S.get (ρ i)).get Λ g v) →
      FunTempl.ownValsAt (fun C => C.ownsAt Λ S) off (cs.map (·.rename ρ)) values
        = FunTempl.ownValsAt (fun C => C.ownsAt Λ T) loff cs values := by
  intro cs
  induction cs with
  | nil => intro values off loff _ _; rw [List.map_nil, ownValsAt_nil_cons, ownValsAt_nil_cons]
  | cons C cs ih =>
    intro values off loff hparam hcoh
    cases values with
    | nil => rw [ownValsAt_nil_values, ownValsAt_nil_values]
    | cons v values =>
      obtain ⟨i, rfl⟩ := hparam C List.mem_cons_self
      have hhead : ((TyConsId.param i).rename ρ).ownsAt Λ S (off ((TyConsId.param i).rename ρ)) v
          = (TyConsId.param i).ownsAt Λ T (loff (TyConsId.param i)) v := by
        have hsel : (TyConsId.selRanks ρ off (TyConsId.param i :: cs) i)[0]?
            = some (off ((TyConsId.param i).rename ρ)) := by
          rw [TyConsId.selRanks, if_pos rfl]
          rfl
        have h0 := hcoh i List.mem_cons_self 0 _ hsel v
        rw [Nat.add_zero] at h0
        rw [TyConsId.rename_param, TyConsId.ownsAt_param, TyConsId.ownsAt_param,
          ← TyConsId.rename_param ρ i]
        exact h0.symm
      rw [List.map_cons, ownValsAt_cons, ownValsAt_cons, hhead]
      refine congrArg _ (ih values _ _
        (fun C' hC' => hparam C' (List.mem_cons_of_mem _ hC')) ?_)
      intro j hj k g hg w
      by_cases hji : j = i
      · subst hji
        have hsel : (TyConsId.selRanks ρ off (TyConsId.param j :: cs) j)[k + 1]? = some g := by
          rw [TyConsId.selRanks, if_pos rfl]
          exact hg
        have h1 := hcoh j List.mem_cons_self (k + 1) g hsel w
        have hb : TyConsId.bumpOff loff (TyConsId.param j) (TyConsId.param j)
            = loff (TyConsId.param j) + 1 := by simp [TyConsId.bumpOff]
        rw [hb, show loff (TyConsId.param j) + 1 + k = loff (TyConsId.param j) + (k + 1) by omega]
        exact h1
      · have hne : TyConsId.param j ≠ TyConsId.param i := by simpa using hji
        have hsel : (TyConsId.selRanks ρ off (TyConsId.param i :: cs) j)[k]? = some g := by
          rw [TyConsId.selRanks, if_neg (Ne.symm hne)]
          exact hg
        have h1 := hcoh j (List.mem_cons_of_mem _ hj) k g hsel w
        have hb : TyConsId.bumpOff loff (TyConsId.param i) (TyConsId.param j)
            = loff (TyConsId.param j) := by simp [TyConsId.bumpOff, hne]
        rw [hb]
        exact h1

/-- When the renaming is injective, the parameters of a source carrying its type parameter
`i` are ranked in the merge exactly as they are ranked inside the source, up to the offset
the merge starts them at: no parameter of the source carrying another type parameter is
counted among them. -/
theorem TyConsId.selRanks_eq_map_range {ρ : TyIdx → TyIdx} {n : ℕ}
    (hinj : ∀ j < n, ∀ j' < n, ρ j = ρ j' → j = j') :
    ∀ (cs : List TyConsId) (off : TyConsId → ℕ) (i : TyIdx), i < n →
      (∀ C ∈ cs, ∃ j < n, C = .param j) →
      selRanks ρ off cs i
        = (List.range (cs.count (TyConsId.param i))).map fun k => off (.param (ρ i)) + k
  | [], off, i, _, _ => rfl
  | C :: cs, off, i, hi, hparam => by
    obtain ⟨j, hj, rfl⟩ := hparam C List.mem_cons_self
    have htail := selRanks_eq_map_range hinj cs
    have hparam' : ∀ C ∈ cs, ∃ j < n, C = TyConsId.param j :=
      fun C hC => hparam C (List.mem_cons_of_mem _ hC)
    by_cases hji : j = i
    · subst hji
      have hb : TyConsId.bumpOff off ((TyConsId.param j).rename ρ)
          = fun D => if D = TyConsId.param (ρ j) then off D + 1 else off D := by
        rw [TyConsId.rename_param]; rfl
      rw [selRanks, if_pos rfl, htail _ j hj hparam', hb, TyConsId.rename_param,
        List.count_cons_self, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, Function.comp_def]
      congr 1
      refine List.map_congr_left fun k _ => ?_
      simp
      omega
    · have hne : ρ j ≠ ρ i := fun h => hji (hinj j hj i hi h)
      have hnec : TyConsId.param j ≠ TyConsId.param i := by simpa using hji
      have hb : TyConsId.bumpOff off ((TyConsId.param j).rename ρ) (TyConsId.param (ρ i))
          = off (TyConsId.param (ρ i)) := by
        rw [TyConsId.rename_param, TyConsId.bumpOff]
        exact if_neg (by simpa using Ne.symm hne)
      rw [selRanks, if_neg hnec, htail _ i hi hparam', hb, List.count_cons_of_ne hnec]

/-- A source bound in a merge along an *injective* renaming, at offsets its type parameters
have not been used at, reads exactly the reindexed typed subvariants of the merge: its
parameters are ranked in the merge as they are ranked inside it. -/
theorem FunTempl.ownValsAt_reindex_of_inj {Λ : Library} {M n : ℕ} (S : SubvArgs.{0} M)
    (ρ : TyIdx → TyIdx) (cs : List TyConsId) (values : List Val) (off : TyConsId → ℕ)
    (hinj : ∀ j < n, ∀ j' < n, ρ j = ρ j' → j = j')
    (hparam : ∀ C ∈ cs, ∃ j < n, C = .param j)
    (hoff : ∀ j < n, off (TyConsId.param (ρ j)) = 0) :
    FunTempl.ownValsAt (fun C => C.ownsAt Λ S) off (cs.map (·.rename ρ)) values
      = FunTempl.ownValsAt (fun C => C.ownsAt Λ (TeleArg.reindex default ρ n S)) (fun _ => 0)
          cs values := by
  refine FunTempl.ownValsAt_select S _ ρ cs values off (fun _ => 0)
    (fun C hC => (hparam C hC).imp fun _ h => h.2) ?_
  intro i hi k g hg v
  have hi' : i < n := by
    obtain ⟨j, hj, hij⟩ := hparam _ hi
    obtain rfl : j = i := by simpa using hij.symm
    exact hj
  rw [TyConsId.selRanks_eq_map_range hinj cs off i hi' hparam] at hg
  obtain ⟨hk, hgk⟩ := List.getElem?_eq_some_iff.mp hg
  rw [List.getElem_map, List.getElem_range] at hgk
  rw [hoff i hi', Nat.zero_add] at hgk
  subst hgk
  rw [SubvArgs.get_reindex hi', Nat.zero_add]

/-! ### Properties of well-typed values via opaque predicates -/

/-- The empty state owns the opaque resource of the unit value at the unit type: `()` is a
well-typed program of type `Ty.unit` producing `Val.unit` from no resources. -/
theorem hProp_empty_opaque_unit (Λ : Library) :
    HProp (∅ : Heap) (.opaque Λ Ty.unit Val.unit) :=
  ⟨.unit, FrameStep.pure rfl, safe_pure⟩

/-- The unit value owns the resources of every subvariant of the placeholder typed
subvariant — the unit type with no subvariant at all — in the empty state: past the empty
list of subvariants, owning is the opaque resource of the unit type. -/
theorem hProp_empty_get_default (Λ : Library) (k : ℕ) :
    HProp ∅ ((default : TypedSubvariants.{0}).get Λ k Val.unit) := by
  show HProp ∅ (TypedSubvariants.get ⟨Ty.unit, []⟩ Λ k Val.unit)
  rw [TypedSubvariants.get_mk_nil]
  exact hProp_empty_opaque_unit Λ

/-! ### Reachability and validity -/

namespace Summary

/-- The semantics of the triple of a summary, unfolded: for every *valid* tuple of typed
subvariants, every state satisfying the postcondition is reached by running the source from
a state satisfying the precondition. -/
theorem uxFrameTriple_triple_iff {ς : Summary} {Λ : Library} {ε : LExit} :
    UXFrameTriple Λ (ς.triple Λ ε) ↔
      ∀ args S r h',
        HProp h' (ς.post r args S) →
          ∃ h, HProp h (ς.pre Λ args S) ∧
            ∃ εₛ, ε.toExit r = some εₛ ∧ FrameStep Λ h (ς.expr args S) h' εₛ := by
  rw [UXFrameTriple, triple, uxTriple_polyTriple]

section Accessors
variable {ς : Summary} {Λ : Library} {τ : TyConsId} {ε : LExit}
/-- The source of a reachable summary produces the type constructor it is filed under, up to
the names of the type parameters. -/
theorem Reachable.src_ty (h : ς.Reachable Λ τ ε) : ς.src.fn.ty.Match τ := h.1
/-- A summary reachable at a type constructor is reachable at every matching one. -/
theorem Reachable.of_match {τ' : TyConsId} (h : ς.Reachable Λ τ ε) (hm : τ.Match τ') :
    ς.Reachable Λ τ' ε := ⟨h.src_ty.trans hm, h.2.1, h.2.2⟩
/-- The source of a reachable summary typechecks. -/
theorem Reachable.typechecks (h : ς.Reachable Λ τ ε) : ς.src.Typechecks Λ := h.2.1
/-- The state `[ε : ς.owned]` is reachable from the source of a reachable summary, for every
valid tuple of typed subvariant arguments. -/
theorem Reachable.triple (h : ς.Reachable Λ τ ε) :
    UXFrameTriple Λ (ς.triple Λ ε) := h.2.2
/-- The under-approximate reading of the triple of a reachable summary. -/
theorem Reachable.triple_apply (h : ς.Reachable Λ τ ε) :
    ∀ args S r h',
      HProp h' (ς.post r args S) →
        ∃ hp, HProp hp (ς.pre Λ args S) ∧
          ∃ εₛ, ε.toExit r = some εₛ ∧ FrameStep Λ hp (ς.expr args S) h' εₛ :=
  uxFrameTriple_triple_iff.mp h.triple
/-- A valid summary is reachable. -/
theorem Valid.reachable (h : ς.Valid Λ τ) : ς.Reachable Λ τ .lok := h.1
/-- The source of a valid summary produces the type constructor it is filed under, up to the
names of the type parameters. -/
theorem Valid.src_ty (h : ς.Valid Λ τ) : ς.src.fn.ty.Match τ := h.reachable.src_ty
/-- A summary valid at a type constructor is valid at every matching one: the naming of the
type parameters is immaterial. -/
theorem Valid.of_match {τ' : TyConsId} (h : ς.Valid Λ τ) (hm : τ.Match τ') : ς.Valid Λ τ' :=
  ⟨h.reachable.of_match hm, h.2⟩
/-- The source of a valid summary has one parameter per input value of its postcondition. -/
theorem Valid.wellShaped (h : ς.Valid Λ τ) : ς.WellShaped := h.2.2
/-- The postcondition of a valid summary is satisfiable. -/
theorem Valid.satOwned (h : ς.Valid Λ τ) : ς.SatOwned := h.2.1
/-- The source of a valid summary typechecks. -/
theorem Valid.typechecks (h : ς.Valid Λ τ) : ς.src.Typechecks Λ := h.reachable.typechecks
/-- The owned resources of a valid summary are reachable by running its source. -/
theorem Valid.triple (h : ς.Valid Λ τ) :
    UXFrameTriple Λ (ς.triple Λ .lok) := h.reachable.triple
/-- The under-approximate reading of the triple of a valid summary. -/
theorem Valid.triple_apply (h : ς.Valid Λ τ) :
    ∀ args S r h',
      HProp h' (ς.post r args S) →
        ∃ hp, HProp hp (ς.pre Λ args S) ∧
          ∃ εₛ, LExit.lok.toExit r = some εₛ ∧ FrameStep Λ hp (ς.expr args S) h' εₛ :=
  h.reachable.triple_apply
/-- The source of a valid summary satisfies `Source.Ok`. -/
theorem Valid.src_ok (h : ς.Valid Λ τ) : ς.src.Ok Λ :=
  h.typechecks.ok h.2.1.choose.fst
end Accessors

/-- The resources required by a summary at a tuple of arguments: one resource per input
value, read through the typed subvariant arguments off the type constructor of the
corresponding parameter of the source. -/
theorem pre_apply (ς : Summary) (Λ : Library) (S : SubvArgs.{0} ς.src.arity)
    (args : TeleArg ς.ownedTele) :
    ς.pre Λ args S =
      FunTempl.ownValsAt (fun C => C.ownsAt Λ S) (fun _ => 0) ς.src.fn.paramCons
        args.snd.toList :=
  rfl
/-- The resources required by a summary, as the abstract reading of the type constructors of
the parameters of its source at its typed subvariant arguments. -/
theorem pre_apply_ownVals (ς : Summary) (Λ : Library) (S : SubvArgs.{0} ς.src.arity)
    (args : TeleArg ς.ownedTele) :
    ς.pre Λ args S = ς.src.fn.ownVals (fun C => C.ownsAt Λ S) args.snd.toList :=
  rfl
/-- A summary source consuming no input value requires no resources. -/
theorem pre_apply_eq_emp (ς : Summary) (Λ : Library) (S : SubvArgs.{0} ς.src.arity)
    (args : TeleArg ς.ownedTele) (h : args.snd.toList = []) : ς.pre Λ args S = .emp := by
  rw [pre_apply, h]; rfl
/-- The expression a summary runs at a tuple of arguments: the body of its source, at the
types of the typed subvariant arguments and with the formal parameters replaced by the input
values. -/
theorem expr_apply (ς : Summary) (S : SubvArgs.{0} ς.src.arity) (args : TeleArg ς.ownedTele) :
    ς.expr args S =
      (ς.src.fn.body args.fst S.tys).substs
        ς.src.fn.paramNames (Term.ofVals args.snd.toList) :=
  rfl
/-- The postcondition of a summary at a tuple of arguments. -/
theorem post_apply (ς : Summary) (S : SubvArgs.{0} ς.src.arity) (r : Val)
    (args : TeleArg ς.ownedTele) : ς.post r args S = ς.ownedAt r args S :=
  rfl

/-- A valid summary inhabits a type constructor of exactly as many type arguments as it
supplies to it. -/
theorem resArity_of_valid {ς : Summary} {Λ : Library} {τ : TyConsId} (h : ς.Valid Λ τ) :
    ς.src.resArity = τ.arity := h.src_ty.arity_eq

/-- The source of a base summary has no parameter. -/
@[simp] theorem base_src_params (kind : BaseTy) : (base kind).src.fn.params = [] := by
  cases kind <;> rfl
/-- The result type constructor of a base summary is the base type it describes. -/
@[simp] theorem base_src_ty (kind : BaseTy) : (base kind).src.fn.ty = TyConsId.base kind := by
  cases kind <;> rfl
/-- A base summary consumes no input value. -/
@[simp] theorem base_valArity (kind : BaseTy) : (base kind).valArity = 0 := by
  cases kind <;> rfl
/-- A base summary has no type parameter, hence no typed subvariant argument. -/
@[simp] theorem base_src_arity (kind : BaseTy) : (base kind).src.arity = 0 := by
  cases kind <;> rfl

/-- The resources a base summary owns: its result is the value its symbolic value
describes. -/
@[simp] theorem base_ownedAt_int (r : Val) (args : TeleArg (base .int).ownedTele)
    (S : SubvArgs.{0} (base .int).src.arity) {h : Heap} :
    HProp h ((base .int).ownedAt r args S) ↔ HProp h (⌞ r = .int args.1 ⌟ : Asrt.{0}) :=
  Iff.rfl
@[simp] theorem base_ownedAt_bool (r : Val) (args : TeleArg (base .bool).ownedTele)
    (S : SubvArgs.{0} (base .bool).src.arity) {h : Heap} :
    HProp h ((base .bool).ownedAt r args S) ↔ HProp h (⌞ r = .bool args.1 ⌟ : Asrt.{0}) :=
  Iff.rfl
@[simp] theorem base_ownedAt_loc (r : Val) (args : TeleArg (base .loc).ownedTele)
    (S : SubvArgs.{0} (base .loc).src.arity) {h : Heap} :
    HProp h ((base .loc).ownedAt r args S) ↔ HProp h (⌞ r = .loc args.1 ⌟ : Asrt.{0}) :=
  Iff.rfl
@[simp] theorem base_ownedAt_unit (r : Val) (args : TeleArg (base .unit).ownedTele)
    (S : SubvArgs.{0} (base .unit).src.arity) {h : Heap} :
    HProp h ((base .unit).ownedAt r args S) ↔ HProp h (⌞ r = .unit ⌟ : Asrt.{0}) :=
  Iff.rfl

theorem base_valid {Λ : Library} {kind : BaseTy} : (base kind).Valid Λ (.base kind) := by
  have hparams : (base kind).src.fn.params = [] := base_src_params kind
  have hvalid : (base kind).src.fn.Valid := by
    refine ⟨by rw [hparams]; simp, ?_⟩
    intro i hi
    rw [base_src_ty kind, TyConsId.params_base] at hi
    exact absurd hi (List.not_mem_nil)
  refine ⟨⟨?tymatch, ⟨hvalid, ?typechecks⟩, ?triple⟩, ?sat, ?shape⟩
  case shape => cases kind <;> rfl
  case tymatch =>
    rw [base_src_ty kind]
  case typechecks =>
    refine fun types args => ⟨?_, ?_, ?_⟩
    · rw [FunTempl.concretise_ty]
      cases kind <;> exact safe_pure
    · rw [FunTempl.concretise_safe]
      cases kind <;> rfl
    · rw [FunImpl.ParamsNodup, FunImpl.paramNames, FunTempl.concretise_params,
        FunTempl.sig_apply_eq_nil hparams, List.map_nil]
      exact List.nodup_nil
  case triple =>
    refine uxFrameTriple_triple_iff.mpr fun args S v h' hΦ => ?_
    rw [post_apply] at hΦ
    refine ⟨∅, ?_, .ok v, rfl, ?_⟩
    · rw [pre_apply_eq_emp _ _ _ _ (by cases kind <;> rfl)]
      rfl
    · rw [expr_apply, FunTempl.paramNames_eq_nil hparams, Expr.substs_nil_left]
      revert hΦ
      cases kind <;> simp only [base_ownedAt_int, base_ownedAt_bool, base_ownedAt_loc,
          base_ownedAt_unit] <;>
        rintro ⟨rfl, rfl⟩ <;> exact FrameStep.pure rfl
  case sat =>
    cases kind
    · exact ⟨⟨0, .unit⟩, PUnit.unit, .int 0, ∅,
        by rw [base_ownedAt_int]; exact ⟨rfl, rfl⟩⟩
    · exact ⟨⟨false, .unit⟩, PUnit.unit, .bool false, ∅,
        by rw [base_ownedAt_bool]; exact ⟨rfl, rfl⟩⟩
    · exact ⟨⟨⟨0, 0⟩, .unit⟩, PUnit.unit, .loc ⟨0, 0⟩, ∅,
        by rw [base_ownedAt_loc]; exact ⟨rfl, rfl⟩⟩
    · exact ⟨.unit, PUnit.unit, .unit, ∅,
        by rw [base_ownedAt_unit]; exact ⟨rfl, rfl⟩⟩

/-! ### The identity summary

The summary `Summary.id` runs the identity function on its single input value.  Its source
has one parameter, carrying the identity type constructor, and one type argument — the
argument of the identity type constructor itself, which is the type of both its parameter
and its result.  That argument is supplied as a typed subvariant, and the identity summary
owns exactly what its input value owns as an inhabitant of it. -/

/-- The signature of the identity source at a type argument: its single parameter `x` gets
that very type. -/
@[simp] theorem id_src_sig (Λ : Library) (τ₀ : Ty) :
    (id Λ).src.fn.sig ⟨τ₀, PUnit.unit⟩ = [("x", τ₀)] := rfl
/-- The identity summary runs the value it is given. -/
@[simp] theorem id_expr (Λ : Library) (S : SubvArgs.{0} 1) (v : Val) :
    (id Λ).expr ⟨v, PUnit.unit⟩ S = Expr.val v := rfl
/-- The identity summary requires of its input value the resources the first subvariant of
the typed subvariant it is given describes. -/
@[simp] theorem id_pre (Λ : Library) (ts : TypedSubvariants.{0}) (v : Val) :
    (id Λ).pre Λ ⟨v, PUnit.unit⟩ ⟨ts, PUnit.unit⟩ = (ts.get Λ 0 v ∗ .emp) := rfl
/-- The identity summary owns what its input value owns at the typed subvariant it is given,
and returns it. -/
@[simp] theorem id_owned (Λ : Library) (ts : TypedSubvariants.{0}) (v r : Val) {h : Heap} :
    HProp h ((id Λ).ownedAt r ⟨v, PUnit.unit⟩ ⟨ts, PUnit.unit⟩) ↔
      HProp h (⌞ r = v ⌟ ∗ ts.get Λ 0 v) :=
  Iff.rfl

/-- The postcondition of the identity summary, read at arbitrary arguments: its result is
its single input value `args.snd.1`, which owns the resources the typed subvariant supplied for
the single type parameter describes at rank `0`. -/
theorem id_ownedAt (Λ : Library) (r : Val) (args : TeleArg (id Λ).ownedTele)
    (S : SubvArgs.{0} (id Λ).src.arity) {h : Heap} :
    HProp h ((id Λ).ownedAt r args S) ↔
      HProp h (⌞ r = args.snd.1 ⌟ ∗ S.1.get Λ 0 args.snd.1) :=
  Iff.rfl

/-- The identity summary is a valid inhabitant of the identity type constructor: it is
structurally valid, has one parameter per input value, produces its own single type
parameter, concretises to a well-typed implementation, satisfies the frame triple relating
its precondition to its owned resources — the resources of a *valid* typed subvariant entail
the opaque predicate of its type — and its postcondition is satisfiable at every tuple of
well-typed input values. -/
theorem id_valid {Λ : Library} : (Summary.id Λ).Valid Λ (.param 0) := by
  refine ⟨⟨rfl, ⟨⟨?params_valid, ?ty_bounded⟩, ?concretise⟩, ?triple⟩, ?sat, ?shape⟩
  case shape => rfl
  case params_valid =>
    intro p hp
    obtain rfl := List.mem_singleton.mp (show p ∈ [("x", TyConsId.param 0)] from hp)
    exact ⟨0, Nat.zero_lt_one, rfl⟩
  case ty_bounded =>
    intro i hi
    obtain rfl := List.mem_singleton.mp (show i ∈ [0] from hi)
    exact Nat.zero_lt_one
  case concretise =>
    rintro ⟨τ₀, ⟨⟩⟩ args
    refine ⟨⟨τ₀, ?_, rfl⟩, rfl, ?_⟩
    · exact VarCtx.from_lookup_some (ps := [("x", τ₀)]) (by simp) (by simp)
    · rw [FunImpl.ParamsNodup, FunImpl.paramNames, FunTempl.concretise_params, id_src_sig]
      simp
  case triple =>
    refine uxFrameTriple_triple_iff.mpr ?_
    rintro ⟨val, ⟨⟩⟩ ⟨ts, ⟨⟩⟩ v h' hΦ
    rw [post_apply, id_owned] at hΦ
    obtain ⟨h₁, h₂, rfl, hdisj, ⟨rfl, rfl⟩, hown⟩ := hΦ
    refine ⟨∅ ∪ h₂, ?_, .ok v, rfl, ?_⟩
    · rw [id_pre]
      exact ⟨h₂, ∅, by rw [PFun.empty_union, PFun.union_empty],
        PFun.disjoint_empty_right h₂, hown, rfl⟩
    · rw [id_expr]
      exact FrameStep.pure rfl
  case sat =>
    refine ⟨⟨Val.unit, PUnit.unit⟩, ⟨Ty.unit, PUnit.unit⟩, Val.unit, ∅, ?_⟩
    show HProp ∅ ((id Λ).ownedAt Val.unit ⟨Val.unit, PUnit.unit⟩ ⟨default, PUnit.unit⟩)
    rw [Summary.id_owned]
    exact ⟨∅, ∅, (PFun.empty_union ∅).symm, PFun.disjoint_empty_left ∅, ⟨rfl, rfl⟩,
      hProp_empty_get_default Λ 0⟩

end Summary

/-! ### Membership in a summary context -/

namespace SummCtx

/-- Matching type constructors are filed under the same index: a summary picked for one of
them is picked for the other. -/
theorem mem_of_match {S : SummCtx} {τ τ' : TyConsId} {ς : Summary}
    (h : S.MemTy τ ς) (hm : τ.Match τ') : S.MemTy τ' ς := by
  rw [SummCtx.MemTy, ← show τ.anon = τ'.anon from hm]
  exact h
/-- A summary just filed for a type constructor may be picked for it — and, by
`SummCtx.mem_of_match`, for every matching type constructor. -/
theorem mem_update_self (S : SummCtx) (τ : TyConsId) (ς : Summary) :
    (S.update τ ς).MemTy τ ς := by
  rw [SummCtx.MemTy, SummCtx.update, Function.update_self]
  exact List.mem_cons_self
/-- A summary of a type space extended by filing one is either that one — filed for a type
constructor matching the one it is looked up at — or a summary of the original space. -/
theorem mem_update {S : SummCtx} {τ τ' : TyConsId} {ς ς' : Summary}
    (h : (S.update τ' ς').MemTy τ ς) : τ.Match τ' ∧ ς = ς' ∨ S.MemTy τ ς := by
  rw [SummCtx.MemTy, SummCtx.update] at h
  by_cases hτ : τ.Match τ'
  · rw [show τ.anon = τ'.anon from hτ, Function.update_self, List.mem_cons] at h
    refine h.imp (fun h => ⟨hτ, h⟩) fun hin => ?_
    rwa [SummCtx.MemTy, show τ.anon = τ'.anon from hτ]
  · rw [Function.update_of_ne hτ] at h
    exact Or.inr h

/-- Filing a summary keeps the summaries already in the type space available. -/
theorem mem_update_of_mem {S : SummCtx} {τ τ' : TyConsId} {ς ς' : Summary}
    (h : S.MemTy τ ς) : (S.update τ' ς').MemTy τ ς := by
  rw [SummCtx.MemTy, SummCtx.update]
  by_cases hτ : τ.Match τ'
  · rw [show τ.anon = τ'.anon from hτ, Function.update_self]
    exact List.mem_cons_of_mem _ (by rwa [SummCtx.MemTy, show τ.anon = τ'.anon from hτ] at h)
  · rw [Function.update_of_ne hτ]
    exact h

theorem base_valid {Λ : Library} : Valid Λ (base Λ) := by
  intro τ ς hin
  simp only [base, List.foldr_cons, List.foldr_nil] at hin
  rcases mem_update hin with ⟨hm, rfl⟩ | hin
  · exact Summary.id_valid.of_match hm.symm
  rcases mem_update hin with ⟨hm, rfl⟩ | hin
  · exact Summary.base_valid.of_match hm.symm
  rcases mem_update hin with ⟨hm, rfl⟩ | hin
  · exact Summary.base_valid.of_match hm.symm
  rcases mem_update hin with ⟨hm, rfl⟩ | hin
  · exact Summary.base_valid.of_match hm.symm
  rcases mem_update hin with ⟨hm, rfl⟩ | hin
  · exact Summary.base_valid.of_match hm.symm
  · exact absurd hin List.not_mem_nil

end SummCtx

@[simp] theorem SubvArgs.ownAssertions_nil {N : ℕ} (T : SubvArgs.{0} N)
    (F : SubvArgs.{0} (Source.mergedFreeArity (([] : List Summary).map Summary.src)))
    (syms : TeleArg (Source.mergedTeleOf (([] : List Summary).map Summary.src)))
    (vals : TeleArg (.uniform Val
      (Source.mergedValArity (([] : List Summary).map Summary.src)))) :
    SubvArgs.ownAssertions T [] F syms vals = [] := rfl

@[simp] theorem SubvArgs.ownAssertions_cons {N : ℕ} (T : SubvArgs.{0} N)
    (ς : Summary) (ςs : List Summary)
    (F : SubvArgs.{0} (Source.mergedFreeArity ((ς :: ςs).map Summary.src)))
    (syms : TeleArg (Source.mergedTeleOf ((ς :: ςs).map Summary.src)))
    (vals : TeleArg (.uniform Val (Source.mergedValArity ((ς :: ςs).map Summary.src)))) :
    SubvArgs.ownAssertions T (ς :: ςs) F syms vals =
      (fun v => ς.ownedAt v
          (TeleArg.app syms.fst
            ((vals.splitUniform ς.src.fn.params.length
                (Source.mergedValArity (ςs.map Summary.src))).1.reindex Val.unit id ς.valArity))
          ((T.appendUniform
              (F.splitUniform ς.src.freeArity
                (Source.mergedFreeArity (ςs.map Summary.src))).1).reindex default id
            ς.src.arity))
        :: SubvArgs.ownAssertions (ς.src.dropSubvArgs T (List.range N)) ςs
            (F.splitUniform ς.src.freeArity (Source.mergedFreeArity (ςs.map Summary.src))).2
            syms.snd
            (vals.splitUniform ς.src.fn.params.length
              (Source.mergedValArity (ςs.map Summary.src))).2 := rfl

/-- There is one assertion per supplied summary. -/
@[simp] theorem SubvArgs.length_ownAssertions {N : ℕ} :
    ∀ (T : SubvArgs.{0} N) (ςs : List Summary)
      (F : SubvArgs.{0} (Source.mergedFreeArity (ςs.map Summary.src)))
      (syms : TeleArg (Source.mergedTeleOf (ςs.map Summary.src)))
      (vals : TeleArg (.uniform Val (Source.mergedValArity (ςs.map Summary.src)))),
      (SubvArgs.ownAssertions T ςs F syms vals).length = ςs.length
  | _, [], _, _, _ => rfl
  | T, ς :: ςs, F, syms, vals => by
      rw [SubvArgs.ownAssertions_cons, List.length_cons, List.length_cons,
        SubvArgs.length_ownAssertions _ ςs]

/-- Reading a component of the typed subvariants left after a bound summary: the same type,
and the subvariants past those of the parameters of `s` carrying a type parameter the selection
`osel` sends to `j`. -/
theorem Source.get_dropSubvArgs {n : ℕ} (S : SubvArgs.{0} n) (s : Source) (osel : List TyIdx)
    {j : ℕ} (hj : j < n) :
    (s.dropSubvArgs S osel).get j = ⟨(S.get j).ty, (S.get j).own.drop (s.selCount osel j)⟩ := by
  rw [Source.dropSubvArgs, SubvArgs.get, TeleArg.toList_ofListPad _ (by simp),
    List.getD_eq_getElem?_getD]
  simp [hj]

/-- At the identity selection, a source consumes, at the component `j`, the subvariants of its
own parameters carrying `j`. -/
theorem Source.selCount_range (s : Source) {n j : ℕ} (hj : j < n) :
    s.selCount (List.range n) j = s.paramCount j := by
  rw [Source.selCount, Source.paramCount, List.count_eq_countP]
  refine List.countP_congr fun C _ => ?_
  cases C with
  | param k =>
    by_cases hk : k < n
    · simp [List.getElem?_range hk]
    · have hnone : (List.range n)[k]? = none :=
        List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hk)
      simp only [hnone]
      simp only [reduceCtorEq, beq_iff_eq, TyConsId.param.injEq, false_iff]
      rintro rfl
      exact hk hj
  | base => simp
  | custom => simp

/-- Reading a component of the typed subvariants left after a source bound at the identity
selection: the same type, and the subvariants past those of the parameters of `s` carrying
`j`. -/
theorem Source.get_dropSubvArgs_range {n : ℕ} (S : SubvArgs.{0} n) (s : Source) {j : ℕ}
    (hj : j < n) :
    (s.dropSubvArgs S (List.range n)).get j
      = ⟨(S.get j).ty, (S.get j).own.drop (s.paramCount j)⟩ := by
  rw [Source.get_dropSubvArgs _ _ _ hj, Source.selCount_range s hj]

/-! ### Counting renamed parameters and reading appended tuples -/

/-- Counting a renamed type parameter among renamed bare type parameters: when exactly `j` is
renamed to `x`, the occurrences of `x` are those of `j`. -/
theorem TyConsId.count_map_rename_param {ρ : TyIdx → TyIdx} {n x j : ℕ} :
    ∀ (cs : List TyConsId), (∀ C ∈ cs, ∃ k < n, C = .param k) →
      (∀ k < n, @Eq ℕ (ρ k) x ↔ k = j) →
      (cs.map (·.rename ρ)).count (.param x) = cs.count (.param j)
  | [], _, _ => rfl
  | C :: cs, hcs, hρ => by
    obtain ⟨k, hk, rfl⟩ := hcs C List.mem_cons_self
    rw [List.map_cons, List.count_cons, List.count_cons,
      TyConsId.count_map_rename_param cs (fun C hC => hcs C (List.mem_cons_of_mem _ hC)) hρ,
      TyConsId.rename_param]
    by_cases hkj : k = j
    · subst hkj; simp [(hρ k hk).mpr rfl]
    · simp [hkj, mt (hρ k hk).mp hkj]

/-- Counting a type parameter no bare type parameter is renamed to: it does not occur. -/
theorem TyConsId.count_map_rename_param_eq_zero {ρ : TyIdx → TyIdx} {n x : ℕ}
    (cs : List TyConsId) (hcs : ∀ C ∈ cs, ∃ k < n, C = .param k) (hρ : ∀ k < n, ¬ @Eq ℕ (ρ k) x) :
    (cs.map (·.rename ρ)).count (.param x) = 0 := by
  rw [TyConsId.count_map_rename_param (j := n) cs hcs fun k hk =>
    ⟨fun h => absurd h (hρ k hk), fun h => absurd h (by omega)⟩]
  refine List.count_eq_zero.mpr fun h => ?_
  obtain ⟨k, hk, hkn⟩ := hcs _ h
  cases hkn
  omega

theorem SubvArgs.get_appendUniform_left {n m : ℕ} (a : SubvArgs.{0} n) (b : SubvArgs.{0} m)
    {j : ℕ} (hj : j < n) :
    SubvArgs.get (TeleArg.appendUniform a b : SubvArgs.{0} (n + m)) j = a.get j := by
  have hi : j < (TeleArg.toList a).length := by rw [TeleArg.toList_length]; exact hj
  rw [SubvArgs.get, SubvArgs.get, TeleArg.toList_appendUniform, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem SubvArgs.get_appendUniform_right {n m : ℕ} (a : SubvArgs.{0} n) (b : SubvArgs.{0} m)
    (j : ℕ) :
    SubvArgs.get (TeleArg.appendUniform a b : SubvArgs.{0} (n + m)) (n + j) = b.get j := by
  have hlen : (TeleArg.toList a).length = n := TeleArg.toList_length a
  have hi : (TeleArg.toList a).length ≤ n + j := by rw [hlen]; exact Nat.le_add_right _ _
  rw [SubvArgs.get, SubvArgs.get, TeleArg.toList_appendUniform, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_right hi, hlen, Nat.add_sub_cancel_left]

end RUXt
