import RUXt.Semantics.Summary.Basic
import RUXt.Semantics.Summary.Source.Specialise
import RUXt.Model.Summary.Derive

/-!
# Deriving a summary for a call

The summary derived for a call on picked summaries (`FunDecl.summary`): its source
`FunDecl.callSource` is an instance of `bindSourcesAux` (`FunDecl.callSource_params`,
`FunDecl.callSource_body_apply`), satisfies its specification (`FunDecl.callSource_spec`),
typechecks (`FunDecl.callSource_typechecks`) and runs the picked sources before the call
(`FunDecl.callSource_frameStep`).  The derived summary is reachable when the call is derivable
in a sound logic (`source_reachable`).
-/

namespace RUXt

/-! ## Properties

### The derived summary -/

/-- The input values of a list of well-shaped picked summaries are the parameters of their
sources. -/
theorem Picks.mergedValArity_srcs : ∀ ςs : Picks, (∀ p ∈ ςs, p.2.WellShaped) →
    Source.mergedValArity (Picks.srcs ςs) = Picks.valArity ςs
  | [], _ => rfl
  | (τ, ς) :: (ςs : Picks), h => by
      show ς.src.fn.params.length + Source.mergedValArity (Picks.srcs ςs)
        = ς.valArity + Picks.valArity ςs
      rw [Picks.mergedValArity_srcs ςs (fun p hp => h p (List.mem_cons_of_mem _ hp)),
        h (τ, ς) List.mem_cons_self]

/-- The largest length of a parameter name of the picked sources. -/
def Picks.maxNameLen (ςs : Picks) : ℕ :=
  List.foldr (fun s => max (RUXt.maxNameLen s.fn.paramNames)) 0 ςs.srcs

namespace FunDecl

variable (φ : FunDecl) (f : Fid) (ςs : Picks)

/-- The renaming apart `FunDecl.callSource` uses: `PVar.freshen`, at a bound on the names of the
called function and of the picked sources. -/
theorem callSource_m :
    (φ.callSource f ςs).fn.params
      = boundParams (max (RUXt.maxNameLen φ.template.paramNames) ςs.maxNameLen)
          φ.template.paramCons φ.tyArity ςs.srcs := rfl

/-- The bound sources fit the parameters they are bound to: each of them names its type
parameters in the order of the anonymous form of the constructor it produces, a constructor
bounded by its type arity and with as many type parameters as the type constructor of the
parameter it is bound to, and that type constructor uses only the first `n` type parameters. -/
def SrcsFit (n : ℕ) (srcs : List Source) (params : List (PVar × TyConsId)) : Prop :=
  List.Forall₂ (fun s p => s.fn.ty.InAnonOrder ∧ s.fn.ty.arity = p.2.arity
    ∧ s.fn.ty.Bounded s.arity ∧ p.2.Bounded n) srcs params

/-- The template of `FunDecl.callSource` has the parameters of `bindSourcesAux` at the renaming
`PVar.freshen`, with the parameters of `φ` as the variables and the free type parameters of the
bound sources starting right after the type parameters of `φ`, whatever the expression the
latter ends in. -/
theorem callSource_params {N : ℕ} (t : RUXt.TyArgs N → Expr) :
    (φ.callSource f ςs).fn.params
      = (bindSourcesAux t (PVar.freshen (max (RUXt.maxNameLen φ.template.paramNames) ςs.maxNameLen))
          φ.template.paramNames φ.template.ty φ.tyArity
          (φ.template.paramCons.map TyConsId.params) ςs.srcs).params :=
  Source.boundParams_eq t _ ςs.srcs φ.template.paramNames φ.tyArity

/-- The body of `FunDecl.callSource` is the body of `bindSourcesAux` at the renaming
`PVar.freshen`, with the call to `f` on the parameters of `φ` as the expression it ends in, the
parameters of `φ` as the variables and the free type parameters of the bound sources starting
right after the type parameters of `φ`, as soon as the picked sources fit the parameters of `φ`
(`FunDecl.SrcsFit`). -/
theorem callSource_body_apply (hfit : SrcsFit φ.tyArity ςs.srcs φ.template.params)
    (args : TeleArg ςs.teleOf) (types : RUXt.TyArgs (φ.tyArity + ςs.freeArity)) :
    (((φ.callSource f ςs).fn.body.apply args).apply types)
      = (((bindSourcesAux
          (fun types => .call f (TyArgs.tyParams types) (Term.ofVars φ.template.paramNames))
          (PVar.freshen (max (RUXt.maxNameLen φ.template.paramNames) ςs.maxNameLen))
          φ.template.paramNames φ.template.ty φ.tyArity
          (φ.template.paramCons.map TyConsId.params) ςs.srcs).body.apply args).apply types) := by
  simp only [callSource, teleBind_apply]
  exact Source.bindSources_eq
    (fun types => .call f (TyArgs.tyParams types) (Term.ofVars φ.template.paramNames)) types
    φ.template.params φ.tyArity ςs.srcs _ args (hfit.imp fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j hj => by unfold RUXt.TyArgs.get; exact TeleArg.getD_toList_block _ _ _ hj)

/-- The source derived for a call produces the result type constructor of the called
function. -/
@[simp] theorem callSource_ty : (φ.callSource f ςs).fn.ty = φ.template.ty := rfl

/-- The source derived for a call is safe. -/
@[simp] theorem callSource_safe : (φ.callSource f ςs).fn.safe = Bool.true := rfl

/-- The source derived for a call on well-shaped picked summaries has one parameter per input
value of a picked summary: the derived summary is run on exactly the input values the picked
summaries consume. -/
theorem callSource_params_length (h : ∀ p ∈ ςs, p.2.WellShaped) :
    (φ.callSource f ςs).fn.params.length = ςs.valArity := by
  rw [callSource_params φ f ςs (fun _ : RUXt.TyArgs 0 => Expr.val .unit),
    Expr.bindSourcesAux_params_length, Picks.mergedValArity_srcs ςs h]

end FunDecl

/-- The summary derived for a call to `f`, the function declared by `φ`, on the picked
summaries `ςs`, whose postcondition is carried by the subvariant `Ψ'` of the shape of the
derivation (`FunDecl.Subvariant.toSubvariant`), and whose source is `FunDecl.callSource`. -/
def FunDecl.summary (φ : FunDecl) (f : Fid) (ςs : Picks) (Ψ' : φ.Subvariant ςs) : Summary :=
  ⟨Ψ'.toSubvariant, (φ.callSource f ςs).fn⟩

@[simp] theorem FunDecl.summary_src (φ : FunDecl) (f : Fid) (ςs : Picks)
    (Ψ' : φ.Subvariant ςs) :
    (φ.summary f ςs Ψ').src = φ.callSource f ςs := rfl

/-- The derived summary takes the input values of the picked summaries. -/
@[simp] theorem FunDecl.summary_valArity (φ : FunDecl) (f : Fid) (ςs : Picks)
    (Ψ' : φ.Subvariant ςs) :
    (φ.summary f ςs Ψ').valArity = ςs.valArity := rfl

/-- The summary derived from well-shaped picked summaries is well-shaped. -/
theorem FunDecl.summary_wellShaped (φ : FunDecl) (f : Fid) (ςs : Picks)
    (Ψ' : φ.Subvariant ςs) (h : ∀ p ∈ ςs, p.2.WellShaped) :
    (φ.summary f ςs Ψ').WellShaped :=
  φ.callSource_params_length f ςs h

/-- The postcondition of the derived summary is the subvariant `Ψ'` of the shape of the
derivation it carries. -/
theorem FunDecl.summary_ownedAt (φ : FunDecl) (f : Fid) (ςs : Picks)
    (Ψ' : φ.Subvariant ςs) (r : Val) (args : TeleArg (φ.summary f ςs Ψ').ownedTele)
    (S : SubvArgs.{0} (φ.summary f ςs Ψ').src.arity) :
    (φ.summary f ςs Ψ').ownedAt r args S = (Ψ' r).at args S := rfl

/-- `FunDecl.summary_ownedAt`, as an equivalence of the heaps the two sides hold of. -/
theorem FunDecl.hProp_summary_ownedAt (φ : FunDecl) (f : Fid) (ςs : Picks)
    (Ψ' : φ.Subvariant ςs) (r : Val) (args : TeleArg (φ.summary f ςs Ψ').ownedTele)
    (S : SubvArgs.{0} (φ.summary f ςs Ψ').src.arity) {h : Heap} :
    HProp h ((φ.summary f ςs Ψ').ownedAt r args S) ↔ HProp h ((Ψ' r).at args S) := Iff.rfl

/-- For the semantic solver, obtaining a subvariant from a derived postcondition is logical
equivalence, at every result value, every tuple of arguments of the derived summary and every
tuple of typed subvariants, with the derived postcondition with the input values of the call
bound. -/
theorem semSolver_simplifiesTo {ςs : Picks} {φ : FunDecl}
    {Ψ : ςs.DerivedPost φ.tyArity} {Φ : φ.Subvariant ςs} :
    Ψ.SimplifiesTo semSolver Φ ↔
      ∀ (r : Val) (args : TeleArg (ςs.teleOf.app (.uniform Val ςs.valArity)))
        (S : SubvArgs.{0} (φ.tyArity + ςs.freeArity)),
        (Φ r).at args S ⊣⊢ .ex fun vs => (Ψ r).at (args.app vs) S := by
  rw [Picks.DerivedPost.SimplifiesTo, semSolver_simplify]
  constructor
  · intro h r args S
    simpa only [polyAsrt_apply, TeleArg.fst_append, TeleArg.snd_append,
      TeleArg.ulower_uliftArg] using
      h ((TeleArg.uliftArg (tt := Tele.cons fun _ : Val => _) ⟨r, args⟩).app S)
  · intro h a
    simp only [polyAsrt_apply]
    exact h _ _ _

/-- The postcondition of the summary derived with a subvariant obtained from the derived
postcondition `Ψ`, applied to the result value and to both tuples of arguments, is `Ψ` with the
input values of the call existentially bound. -/
theorem Picks.DerivedPost.SimplifiesTo.ownedAt {ςs : Picks} {f : Fid} {φ : FunDecl}
    {Ψ : ςs.DerivedPost φ.tyArity} {Ψ' : φ.Subvariant ςs}
    (h : Ψ.SimplifiesTo semSolver Ψ')
    (r : Val) (args : TeleArg (φ.summary f ςs Ψ').ownedTele)
    (S : SubvArgs.{0} (φ.tyArity + ςs.freeArity)) :
    (φ.summary f ςs Ψ').ownedAt r args S ⊣⊢
      .ex fun vs => PolyAsrt.at (Ψ r) (args.app vs) S :=
  semSolver_simplifiesTo.mp h r args S

theorem Picks.le_maxNameLen {ςs : Picks} {s : Source} (h : s ∈ ςs.srcs)
    {x : PVar} (hx : x ∈ s.fn.paramNames) : x.length ≤ ςs.maxNameLen := by
  rw [Picks.maxNameLen]
  generalize ςs.srcs = srcs at h ⊢
  induction srcs with
  | nil => simp at h
  | cons t ts ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (RUXt.le_maxNameLen hx) (le_max_left _ _)
    · exact le_trans (ih h) (le_max_right _ _)

namespace Picks

/-! ### The derived call and its postcondition -/

/-- A call derivable in a *sound* logic is a sound triple: the typed subvariants being
symbolic values of it, the single derivation covers every tuple of them
(`uxTriple_poly`). -/
theorem DerivableCall.uxFrameTriple {ςs : Picks} {L : Logic.{0}} (hL : L.Sound)
    {Λ : Library} {f : Fid} {tyArity : ℕ} {ε : LExit} {Ψ : ςs.DerivedPost tyArity}
    (h : ςs.DerivableCall L Λ f ε Ψ) :
    UXFrameTriple Λ ⟨ςs.mergeOwned Λ tyArity, ςs.mergeCall f Λ tyArity, ε, Ψ⟩ :=
  hL h

/-! ### The picked summaries and their sources -/

@[simp] theorem srcs_cons (τ : TyConsId) (ς : Summary) (ςs : Picks) :
    srcs ((τ, ς) :: ςs) = ς.src :: ςs.srcs := rfl
/-- There is one merged source per picked summary. -/
@[simp] theorem length_srcs (ςs : Picks) : ςs.srcs.length = ςs.length := List.length_map _

/-- The sources of valid picked summaries meet the requirements of the construction. -/
theorem srcs_ok {Λ : Library} {ςs : Picks} (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ) :
    ∀ s ∈ ςs.srcs, s.Ok Λ := by
  intro s hs
  obtain ⟨⟨τ, ς⟩, hmem, rfl⟩ := List.mem_map.mp hs
  exact (hvalid τ ς hmem).src_ok

/-! ### Properties of the merge functions -/

/-- The typed subvariant arguments `merge` hands to the head summary `ς`, picked for `τ`: the
components of the block `T` of the type parameters of the called function at the type
parameters of `τ`, followed by its own block `own` of free ones. -/
abbrev headSubvs (τ : TyConsId) (ς : Summary) {N : ℕ} (T : SubvArgs.{0} N)
    (own : SubvArgs.{0} ς.src.freeArity) : SubvArgs.{0} ς.src.arity :=
  ((T.reindex default (τ.params.getD · 0) τ.arity).appendUniform own).reindex default id
    ς.src.arity

/-- The head summary of a merge reads the typed subvariant supplied for a type parameter of the
type constructor it is picked for at the position of that type parameter. -/
theorem headSubvs_get_param (τ : TyConsId) (ς : Summary) {N : ℕ} (T : SubvArgs.{0} N)
    (own : SubvArgs.{0} ς.src.freeArity) {j : ℕ}
    (hj : j < τ.arity) (hn : τ.arity + ς.src.freeArity = ς.src.arity) :
    (headSubvs τ ς T own).get j = T.get (τ.params.getD j 0) := by
  rw [headSubvs, SubvArgs.get, TeleArg.toList_reindex_id _ _ hn, ← SubvArgs.get,
    SubvArgs.get_appendUniform_left _ _ hj, SubvArgs.get_reindex hj]

/-- One step of a merge: the tuple of typed subvariants is split into the block of the type
parameters of the called function and the block of the free ones, the head summary reads its
arguments off the two blocks (`Picks.headSubvs`), and the remaining summaries are merged at the
two blocks joined back, with the subvariants of the head summary consumed. -/
theorem merge_cons {X : Type _} (Λ : Library) (x : X) f (τ : TyConsId) (ς : Summary)
    (ςs : Picks) {N : ℕ} (S : SubvArgs.{0} (N + (ς.src.freeArity + ςs.freeArity)))
    (args : TeleArg (tripleTele ((τ, ς) :: ςs))) :
    merge Λ x f ((τ, ς) :: ςs) S args
      = f ς
          (args.snd.splitUniform ςs.size 1).2.1
          args.fst.fst.fst
          (headSubvs τ ς (S.splitUniform N _).1
            ((S.splitUniform N _).2.splitUniform ς.src.freeArity ςs.freeArity).1)
          (args.fst.snd.splitUniform ς.valArity ςs.valArity).1
          (ςs.merge Λ x f
            ((ς.src.dropSubvArgs (S.splitUniform N _).1 τ.params).appendUniform
              ((S.splitUniform N _).2.splitUniform ς.src.freeArity ςs.freeArity).2)
            ((args.fst.fst.snd.app
                (args.fst.snd.splitUniform ς.valArity ςs.valArity).2).app
              (args.snd.splitUniform ςs.size 1).1)) := rfl

/-- The type arguments of the call on the picked summaries: the types of the typed
subvariants supplied for the first `N` type parameters of the derived source, the ones
belonging to the called function. -/
def mergeTys (ςs : Picks) (N : ℕ) (S : SubvArgs.{0} (N + ςs.freeArity)) :
    TeleLift ςs.tripleTele (List Ty) :=
  teleLift fun _ => TyArgs.tyParams S.tys

/-- The results of the picked summaries: the input values of the call. -/
def mergeVals (ςs : Picks) (Λ : Library) (N : ℕ) (S : SubvArgs.{0} (N + ςs.freeArity)) :
    TeleLift ςs.tripleTele (List Val) :=
  teleLift (ςs.merge Λ [] (fun _ r _ _ _ rs => r :: rs) S)

private theorem mergeVals_length_aux (Λ : Library) : ∀ (ςs : Picks) {N : ℕ}
    (S : SubvArgs.{0} (N + ςs.freeArity)) (args : TeleArg ςs.tripleTele),
    (ςs.merge Λ [] (fun _ r _ _ _ rs => r :: rs) S args).length = ςs.length
  | [], _, _, _ => rfl
  | (τ, ς) :: ςs, _, S, args => by
      rw [merge_cons]
      show (_ :: _).length = _
      rw [List.length_cons, mergeVals_length_aux Λ ςs _ _, List.length_cons]

theorem mergeVals_length (ςs : Picks) (Λ : Library) (N : ℕ)
    (S : SubvArgs.{0} (N + ςs.freeArity)) (args : TeleArg ςs.tripleTele) :
    ((ςs.mergeVals Λ N S).at args).length = ςs.length := by
  rw [mergeVals, teleLift_at]
  exact mergeVals_length_aux Λ ςs _ args

/-- The merged call, written with its type and value projections. -/
theorem mergeCall_eq (ςs : Picks) (f : Fid) (Λ : Library) (N : ℕ)
    (S : SubvArgs.{0} (N + ςs.freeArity)) (args : TeleArg ςs.tripleTele) :
    PolyExpr.at (ςs.mergeCall f Λ N) args S =
      .call f ((ςs.mergeTys N S).at args) (Term.ofVals ((ςs.mergeVals Λ N S).at args)) := by
  rw [mergeCall, polyExpr_at, mergeTys, mergeVals, teleLift_at, teleLift_at]

/-! ### Fitting the picked summaries to the parameters of a call -/

/-- The type parameters the call prescribes for the picked summaries: those the type
constructor each summary is picked for uses. -/
def sels (ςs : Picks) : List (List TyIdx) := ςs.tyCons.map TyConsId.params

variable {ςs : Picks} {φ : FunDecl}

@[simp] theorem tyCons_cons (τ : TyConsId) (ς : Summary) (ςs : Picks) :
    tyCons ((τ, ς) :: ςs) = τ :: ςs.tyCons := rfl
@[simp] theorem sels_cons (τ : TyConsId) (ς : Summary) (ςs : Picks) :
    sels ((τ, ς) :: ςs) = τ.params :: ςs.sels := rfl
@[simp] theorem length_tyCons (ςs : Picks) : ςs.tyCons.length = ςs.length :=
  List.length_map _

/-- The type parameters the call prescribes for the picked summaries are those of the type
constructors of the parameters of the called function. -/
theorem sels_eq_callSels (hcons : ςs.tyCons = φ.template.paramCons) :
    ςs.sels = Expr.callSels φ := by
  rw [sels, hcons]

/-- One summary is picked per parameter of the called function. -/
theorem length_eq_of_tyCons_eq (hcons : ςs.tyCons = φ.template.paramCons) :
    φ.template.params.length = ςs.length := by
  have := congrArg List.length hcons
  rw [length_tyCons, FunTempl.length_paramCons] at this
  exact this.symm

/-! ### The type parameters prescribed for the picked summaries -/

/-- The type parameters prescribed for a list of picked summaries — those the type
constructors they are filed under use — are usable from any position `base` at or beyond
`n`, as soon as those type constructors are bounded by `n` and each summary uses as many
type parameters as the constructor it is filed under. -/
private theorem selsOk_aux {n : ℕ} : ∀ (ςs : Picks) (base : ℕ),
    n ≤ base → (∀ C ∈ ςs.tyCons, C.Bounded n) →
    (∀ τ ς, (τ, ς) ∈ ςs → ς.src.tyArity = τ.arity) →
    Source.SelsOk ςs.srcs ςs.sels base
  | [], _, _, _, _ => trivial
  | (τ, ς) :: ςs, base, hbase, hb, harity => by
      refine ⟨fun j hj => ?_, ?_, ?_⟩
      · exact Nat.lt_of_lt_of_le (hb τ (by simp) j hj) hbase
      · exact le_of_eq (harity τ ς (by simp))
      · exact selsOk_aux ςs (base + ς.src.freeArity)
          (le_trans hbase (Nat.le_add_right _ _))
          (fun C' hC' => hb C' (List.mem_cons_of_mem _ hC'))
          (fun τ' ς' h => harity τ' ς' (List.mem_cons_of_mem _ h))

/-- The type parameters the call prescribes for the picked summaries are usable: they are
type parameters of the called function, hence already bound where the source is bound, and
there are exactly as many of them as the type constructor of the summary uses. -/
theorem selsOk {Λ : Library} (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ) (hbounded : φ.Bounded)
    (hcons : ςs.tyCons = φ.template.paramCons) :
    Source.SelsOk ςs.srcs ςs.sels φ.tyArity := by
  refine selsOk_aux ςs φ.tyArity le_rfl ?bounded ?arity
  case bounded =>
    intro C hC
    rw [hcons] at hC
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC
    exact hbounded.param hp
  case arity =>
    intro τ ς hp
    exact Summary.tyArity_of_valid (hvalid τ ς hp)

/-! ### The types the picked sources produce -/

/-- The types a list of picked summaries produces are the instantiations of the type
constructors they are filed under. -/
private theorem resTys_aux {Λ : Library} {N : ℕ} (types : TyArgs N) :
    ∀ (ςs : Picks) (base : ℕ), (∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ) →
      Source.resTys ςs.srcs ςs.sels base types
        = ςs.tyCons.map fun C => C.concretise types
  | [], _, _ => rfl
  | (τ, ς) :: ςs, base, hvalid => by
      have hv := hvalid τ ς (by simp)
      rw [srcs_cons, sels_cons, tyCons_cons, Source.resTys_cons, List.map_cons]
      simp only [List.headD_cons, List.tail_cons]
      refine congrArg₂ List.cons ?head ?tail
      case head =>
        rw [hv.src_ok.resTy_apply_eq, Source.resTyAt, Source.ren,
          TyConsId.rename_mergeRen hv.src_ty]
      case tail =>
        exact resTys_aux types ςs (base + ς.src.freeArity)
          (fun c' ς' h => hvalid c' ς' (List.mem_cons_of_mem _ h))

/-- The types the picked sources produce are exactly the parameter types of the call. -/
theorem resTys_eq_paramTypes {Λ : Library} (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ)
    (hbounded : φ.Bounded) (hcons : ςs.tyCons = φ.template.paramCons)
    (types : TyArgs (φ.tyArity + ςs.freeArity)) :
    Source.resTys ςs.srcs ςs.sels φ.tyArity types
      = φ.paramTypes (types.splitUniform φ.tyArity ςs.freeArity).1 := by
  rw [resTys_aux types ςs φ.tyArity hvalid, hcons, FunDecl.paramTypes, FunTempl.paramTys_apply]
  refine List.map_congr_left fun C hC => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC
  exact (TyConsId.concretise_splitUniform_left (hbounded.param hp) types).symm

/-! ### The operational behaviour of the merged source of a call -/

/-- The subvariants a picked summary consumes from the block of the type parameters of the called
function are those of its parameters in the derived source: a source bound at the selection
`τ.params` (`Source.selCount`) has, at the component `i` of that block, as many parameters as the
parameters of the derived source it contributes (`Source.renCons`) carrying `i`. -/
theorem selCount_eq_count_renCons {Λ : Library} {τ : TyConsId} {ς : Summary}
    (hς : ς.Valid Λ τ) (hord : ς.src.fn.ty.InAnonOrder) {N B : ℕ}
    (hNB : N ≤ B) {i : ℕ} (hi : i < N) :
    ς.src.selCount τ.params i = (ς.src.renCons τ.params B).count (.param i) := by
  have hK : ς.src.fn.ty.arity = τ.arity := hς.src_ty.arity_eq
  have hparam : ∀ C ∈ ς.src.fn.paramCons, ∃ k < ς.src.arity, C = .param k :=
    List.forall_mem_map.mpr hς.typechecks.src_valid.1
  rw [Source.selCount, Source.renCons, List.count_eq_countP, List.countP_map]
  refine List.countP_congr fun C hC => ?_
  obtain ⟨k, hk, rfl⟩ := hparam C hC
  rw [Function.comp_apply, TyConsId.rename_param,
    Source.ren_of_inAnonOrder_sel ς.src hord hK τ.params B hk]
  simp only [beq_iff_eq, TyConsId.param.injEq]
  split_ifs with hkτ
  · have hkτ' : k < τ.params.length := hkτ
    rw [List.getElem?_eq_getElem hkτ', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkτ',
      Option.getD_some, Option.some_inj]
  · have hkτ' : τ.params.length ≤ k := Nat.le_of_not_lt hkτ
    rw [List.getElem?_eq_none hkτ']
    simp only [reduceCtorEq, false_iff]
    intro heq
    have heq' : B + (k - τ.arity) = i := heq
    omega

/-- The picked summaries run their sources one after the other on the input values of the
call: the resources their postconditions describe are produced by running the sources.  The
sources are run on any tuple `values'` with the same components as the input values.

The merge is at a tuple `S` of typed subvariants: those of the `N` type parameters of the called
function, followed by those of the free type parameters of the picked sources, from the type
parameter `B` of the derived source on.  They are those of the derived source, `S₀`, with the
subvariants of the parameters of the summaries already visited consumed (`Source.dropSubvArgs`),
as many at each component as the offsets `off`. -/
theorem merge_runs {Λ : Library} {M : ℕ} (S₀ : SubvArgs.{0} M) {N : ℕ} :
    ∀ (ςs : Picks) (B : ℕ) (args : TeleArg ςs.teleOf) (S : SubvArgs.{0} (N + ςs.freeArity))
      (off : TyConsId → ℕ)
      (values : TeleArg (Tele.uniform Val ςs.valArity))
      (values' : TeleArg (Tele.uniform Val (Source.mergedValArity ςs.srcs)))
      (rvals : TeleArg (Tele.uniform Val ςs.size)) (h : Heap),
      values.toList = values'.toList →
      (∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ) →
      (∀ τ ς, (τ, ς) ∈ ςs → ς.src.fn.ty.InAnonOrder) →
      (∀ τ ς, (τ, ς) ∈ ςs → ∀ i ∈ τ.params, i < N) →
      N ≤ B →
      (∀ i < N, S.get i = ⟨(S₀.get i).ty, (S₀.get i).own.drop (off (.param i))⟩) →
      (∀ j < ςs.freeArity, S.get (N + j)
        = ⟨(S₀.get (B + j)).ty, (S₀.get (B + j)).own.drop (off (.param (B + j)))⟩) →
      HProp h (ςs.merge Λ .emp
        (fun ς r vs Ss rs P => ς.ownedAt r (vs |>.app rs) Ss ∗ P) S
        (args |>.app values |>.app rvals)) →
      ∃ g, Source.Runs Λ (fun C => C.ownsAt Λ S₀) S₀.tys ςs.srcs off ςs.sels B args values'
        (ςs.merge Λ [] (fun _ r _ _ _ rs => r :: rs) S
          (args |>.app values |>.app rvals))
        g h := by
  intro ςs
  induction ςs with
  | nil =>
    intro B args S off values values' rvals h _ _ _ _ _ _ _ hpost
    obtain rfl : h = ∅ := hpost
    exact ⟨∅, Source.runs_nil.mpr ⟨rfl, rfl, rfl⟩⟩
  | cons p ςs ih =>
    obtain ⟨τ, ς⟩ := p
    intro B args S off values values' rvals h hv hvalid hord hτN hNB hS hSF hpost
    -- The two blocks the step splits the tuple into.
    set T : SubvArgs.{0} N := (S.splitUniform N (ς.src.freeArity + Picks.freeArity ςs)).1
      with hTdef
    set F : SubvArgs.{0} (ς.src.freeArity + Picks.freeArity ςs) :=
      (S.splitUniform N (ς.src.freeArity + Picks.freeArity ςs)).2 with hFdef
    have hT : ∀ i < N, T.get i = ⟨(S₀.get i).ty, (S₀.get i).own.drop (off (.param i))⟩ :=
      fun i hi => by rw [hTdef, SubvArgs.get_splitUniform_left _ hi]; exact hS i hi
    have hF : ∀ j < ς.src.freeArity + Picks.freeArity ςs, F.get j
        = ⟨(S₀.get (B + j)).ty, (S₀.get (B + j)).own.drop (off (.param (B + j)))⟩ :=
      fun j hj => by rw [hFdef, SubvArgs.get_splitUniform_right]; exact hSF j hj
    have hς : ς.Valid Λ τ := hvalid τ ς List.mem_cons_self
    have hord₀ : ς.src.fn.ty.InAnonOrder := hord τ ς List.mem_cons_self
    have hτN' : ∀ i ∈ τ.params, i < N := hτN τ ς List.mem_cons_self
    have hK : ς.src.fn.ty.arity = τ.arity := hς.src_ty.arity_eq
    have hn : τ.arity + ς.src.freeArity = ς.src.arity := by
      rw [← hK]; exact TyConsId.arity_add_freeArity hς.typechecks.ty_bounded
    have hparam : ∀ C ∈ ς.src.fn.paramCons, ∃ k < ς.src.arity, C = .param k :=
      List.forall_mem_map.mpr hς.typechecks.src_valid.1
    -- The embedding of the type parameters of the head summary: the type parameters of `τ`,
    -- then a shift of the free ones.
    set ρ := ς.src.ren τ.params B with hρdef
    have hρ : ∀ j < ς.src.arity,
        ρ j = if j < τ.arity then τ.params.getD j 0 else B + (j - τ.arity) :=
      fun j hj => Source.ren_of_inAnonOrder_sel ς.src hord₀ hK τ.params B hj
    have hgetD : ∀ j (hj : j < τ.arity), τ.params.getD j 0 = τ.params[j]'hj := fun j hj => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have hτlt : ∀ j < τ.arity, τ.params.getD j 0 < N := fun j hj => by
      rw [hgetD j hj]
      exact hτN' _ (List.getElem_mem _)
    have hinj : ∀ j < ς.src.arity, ∀ j' < ς.src.arity, ρ j = ρ j' → j = j' := by
      intro j hj j' hj' hjj
      have hjj' : @Eq ℕ (ρ j) (ρ j') := hjj
      rw [hρ j hj, hρ j' hj'] at hjj'
      split_ifs at hjj' with h1 h2 h2
      · rw [hgetD j h1, hgetD j' h2] at hjj'
        exact (List.Nodup.getElem_inj_iff (TyConsId.params_nodup τ)).mp hjj'
      · have h3 := hτlt j h1
        rw [hjj'] at h3
        exact absurd h3 (Nat.not_lt.mpr (le_trans hNB (Nat.le_add_right _ _)))
      · have h3 := hτlt j' h2
        rw [← hjj'] at h3
        exact absurd h3 (Nat.not_lt.mpr (le_trans hNB (Nat.le_add_right _ _)))
      · have h4 : B + (j - τ.arity) = B + (j' - τ.arity) := hjj'
        omega
    -- The typed subvariant arguments the head summary is read at.
    set Fs := F.splitUniform ς.src.freeArity (Picks.freeArity ςs) with hFs
    set P := headSubvs τ ς T Fs.1 with hPdef
    have hPS₀ : ∀ j < ς.src.arity, P.get j
        = ⟨(S₀.get (ρ j)).ty, (S₀.get (ρ j)).own.drop (off (.param (ρ j)))⟩ := by
      intro j hj
      rw [hPdef, headSubvs, SubvArgs.get, TeleArg.toList_reindex_id _ _ hn, ← SubvArgs.get,
        hρ j hj]
      split_ifs with h1
      · rw [SubvArgs.get_appendUniform_left _ _ h1, SubvArgs.get_reindex h1]
        exact hT _ (hτlt j h1)
      · obtain ⟨k, rfl⟩ : ∃ k, j = τ.arity + k := ⟨j - τ.arity, by omega⟩
        rw [SubvArgs.get_appendUniform_right, Nat.add_sub_cancel_left, hFs,
          SubvArgs.get_splitUniform_left _ (by omega)]
        exact hF k (by show k < ς.src.freeArity + _; omega)
    -- The parameters of the head summary are ranked in the derived source from the offsets
    -- `off`, and read, at the tuple `P`, the very subvariants they are ranked at.
    have hcoh : ∀ i, TyConsId.param i ∈ ς.src.fn.paramCons → ∀ k g,
        (TyConsId.selRanks ρ off ς.src.fn.paramCons i)[k]? = some g →
        ∀ v, (P.get i).get Λ ((fun _ => 0 : TyConsId → ℕ) (.param i) + k) v
          = (S₀.get (ρ i)).get Λ g v := by
      intro i hi k g hg v
      obtain ⟨_, hi', ⟨⟩⟩ := hparam _ hi
      rw [TyConsId.selRanks_eq_map_range hinj _ off i hi' hparam] at hg
      obtain ⟨hk, hgk⟩ := List.getElem?_eq_some_iff.mp hg
      rw [List.getElem_map, List.getElem_range] at hgk
      subst hgk
      rw [Nat.zero_add, hPS₀ i hi']
      simp only [TypedSubvariants.get, List.getElem?_drop]
    have hpre_eq : ∀ vs : List Val,
        FunTempl.ownValsAt (fun C => C.ownsAt Λ S₀) off (ς.src.renCons τ.params B) vs
          = FunTempl.ownValsAt (fun C => C.ownsAt Λ P) (fun _ => 0) ς.src.fn.paramCons vs :=
      fun vs => FunTempl.ownValsAt_select S₀ P ρ _ vs off (fun _ => 0)
        (fun C hC => (hparam C hC).imp fun _ h => h.2) hcoh
    -- The types of `P` are the type arguments the source construction runs the head source at.
    have htys : P.tys = ς.src.tyArgs τ.params B S₀.tys := by
      refine TyArgs.ext fun i hi => ?_
      rw [SubvArgs.get_tys, Source.tyArgs, TyArgs.get_reindex hi, SubvArgs.get_tys, hPS₀ i hi]
    -- The remaining summaries read the block of the type parameters of the called function with
    -- the subvariants of the parameters of the head summary consumed, and the remaining free
    -- ones.
    have hT' : ∀ i < N, (ς.src.dropSubvArgs T τ.params).get i
        = ⟨(S₀.get i).ty, (S₀.get i).own.drop
            (TyConsId.offAfter off (ς.src.renCons τ.params B) (.param i))⟩ := by
      intro i hi
      rw [Source.get_dropSubvArgs _ _ _ hi, hT i hi, List.drop_drop, TyConsId.offAfter,
        selCount_eq_count_renCons hς hord₀ hNB hi]
    have hF' : ∀ j < Picks.freeArity ςs, SubvArgs.get Fs.2 j
        = ⟨(S₀.get (B + ς.src.freeArity + j)).ty, (S₀.get (B + ς.src.freeArity + j)).own.drop
            (TyConsId.offAfter off (ς.src.renCons τ.params B)
              (.param (B + ς.src.freeArity + j)))⟩ := by
      intro j hj
      rw [hFs, SubvArgs.get_splitUniform_right,
        hF _ (Nat.add_lt_add_left hj _),
        show B + (ς.src.freeArity + j) = B + ς.src.freeArity + j by omega,
        TyConsId.offAfter, Source.renCons,
        TyConsId.count_map_rename_param_eq_zero _ hparam fun k hk => by
          rw [Source.ren_of_inAnonOrder_sel ς.src hord₀ hK τ.params B hk]
          intro heq
          split_ifs at heq with h1
          · have h3 := hτlt k h1
            rw [heq] at h3
            exact absurd h3 (Nat.not_lt.mpr (by omega))
          · have heq' : B + (k - τ.arity) = B + ς.src.freeArity + j := heq
            omega,
        Nat.add_zero]
    have hw : ς.src.fn.params.length = ς.valArity := hς.wellShaped
    have hfst : (TeleArg.splitUniform ς.src.fn.params.length
          (Source.mergedValArity (srcs ςs)) values').1.toList
        = (TeleArg.splitUniform ς.valArity (valArity ςs) values).1.toList := by
      rw [TeleArg.toList_splitUniform_left, TeleArg.toList_splitUniform_left, ← hv, hw]
    have hsnd : (TeleArg.splitUniform ς.valArity (valArity ςs) values).2.toList
        = (TeleArg.splitUniform ς.src.fn.params.length
            (Source.mergedValArity (srcs ςs)) values').2.toList := by
      rw [TeleArg.toList_splitUniform_right, TeleArg.toList_splitUniform_right, ← hv, hw]
    rw [merge_cons] at hpost ⊢
    simp only [TeleArg.fst_append, TeleArg.snd_append] at hpost ⊢
    obtain ⟨h₁, h₂, rfl, hdisj12, hpost1, hpost2⟩ := hpost
    obtain ⟨g₂, hruns2⟩ := ih (B + ς.src.freeArity) args.snd _
      (TyConsId.offAfter off (ς.src.renCons τ.params B))
      (TeleArg.splitUniform ς.valArity (valArity ςs) values).2
      (TeleArg.splitUniform ς.src.fn.params.length
        (Source.mergedValArity (srcs ςs)) values').2
      (TeleArg.splitUniform (size ςs) 1 rvals).1 h₂ hsnd
      (fun c' ς' hm => hvalid c' ς' (List.mem_cons_of_mem _ hm))
      (fun c' ς' hm => hord c' ς' (List.mem_cons_of_mem _ hm))
      (fun c' ς' hm => hτN c' ς' (List.mem_cons_of_mem _ hm))
      (by omega)
      (fun i hi => by rw [SubvArgs.get_appendUniform_left _ _ hi]; exact hT' i hi)
      (fun j hj => by rw [SubvArgs.get_appendUniform_right]; exact hF' j hj) hpost2
    obtain ⟨g₁, hpre1, -, ⟨⟩, hstep1⟩ :=
      hς.triple_apply _ P (TeleArg.splitUniform (size ςs) 1 rvals).2.1 h₁
        (by rw [Summary.post_apply]; exact hpost1)
    rw [Summary.pre_apply, ← hpre_eq] at hpre1
    rw [Summary.expr_apply, htys] at hstep1
    simp only [TeleArg.fst_append, TeleArg.snd_append] at hpre1 hstep1
    rw [← hfst] at hpre1 hstep1
    exact ⟨g₁ ∪ g₂, Source.runs_cons.mpr
      ⟨(TeleArg.splitUniform (size ςs) 1 rvals).2.1, _, g₁, g₂, h₁, h₂,
        rfl, rfl, rfl, hdisj12, hpre1, hstep1, hruns2⟩⟩

theorem mergeOwned_runs {Λ : Library} (ςs : Picks) (N : ℕ)
    (args : TeleArg ςs.teleOf)
    (S : SubvArgs.{0} (N + ςs.freeArity))
    (values : TeleArg (Tele.uniform Val ςs.valArity))
    (values' : TeleArg (Tele.uniform Val (Source.mergedValArity ςs.srcs)))
    (rvals : TeleArg (Tele.uniform Val ςs.size)) (h : Heap)
    (hv : values.toList = values'.toList)
    (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ)
    (hord : ∀ τ ς, (τ, ς) ∈ ςs → ς.src.fn.ty.InAnonOrder)
    (hτN : ∀ τ ς, (τ, ς) ∈ ςs → ∀ i ∈ τ.params, i < N)
    (hpost : HProp h
      (PolyAsrt.at (ςs.mergeOwned Λ N) (args |>.app values |>.app rvals) S)) :
    ∃ g, Source.Runs Λ (fun C => C.ownsAt Λ S) S.tys ςs.srcs (fun _ => 0) ςs.sels N args values'
      ((ςs.mergeVals Λ N S).at (args |>.app values |>.app rvals)) g h := by
  rw [mergeOwned, polyAsrt_at] at hpost
  rw [mergeVals, teleLift_at]
  exact merge_runs S ςs N args S (fun _ => 0) values values' rvals h hv hvalid hord hτN le_rfl
    (fun _ _ => rfl) (fun _ _ => rfl) hpost

end Picks

/-! ### The merged source of a call -/

namespace FunDecl

open Picks

/-! ### The specification of the merged source of a call -/

/-- The specification of the template binding the picked summaries around a call: it is
structurally valid, it produces the result type of the call, it has one parameter per input
value of a picked summary, its parameters are pairwise distinct and distinct from every name of
the called function and of a picked source, and its body is a well-typed program whenever the
call is. -/
structure BindCallSourcesSpec (Λ : Library) (φ : FunDecl) (f : Fid) (ςs : Picks)
    (types : RUXt.TyArgs (φ.tyArity + ςs.freeArity)) : Prop where
  /-- The merged template is structurally valid. -/
  valid : ((φ.callSource f ςs).fn).Valid
  /-- The merged template produces the result type of the call. -/
  resTy_apply_eq : ((φ.callSource f ςs).fn).resTy.apply types
    = φ.resTy (types.splitUniform φ.tyArity ςs.freeArity).1
  /-- The merged template has one parameter per input value of a picked summary. -/
  params_length : ((φ.callSource f ςs).fn).params.length = ςs.valArity
  /-- The parameters of the merged template are fresh: longer than every name of the called
  function and of a picked source. -/
  paramNames_fresh : ∀ x ∈ ((φ.callSource f ςs).fn).paramNames,
    ¬ x.length ≤ max (RUXt.maxNameLen φ.paramNames) ςs.maxNameLen
  /-- The parameters of the merged template are pairwise distinct. -/
  paramNames_nodup : ((φ.callSource f ςs).fn).paramNames.Nodup
  /-- The body of the merged template is a well-typed program whenever the call it ends in
  is one in the variable context extended by the types the picked summaries produce. -/
  safe : ∀ (args : TeleArg ςs.teleOf) (ν : VarCtx) (τ : Ty),
    (∀ x τx, (x, τx) ∈ ((φ.callSource f ςs).fn).sig.apply types → ν x = Part.some τx) →
    SafeProgram (ν.extend φ.paramNames
        (φ.paramTypes (types.splitUniform φ.tyArity ςs.freeArity).1)) Λ τ
      (.call f (types.splitUniform φ.tyArity ςs.freeArity).1.toList
        (Term.ofVars φ.paramNames)) →
    SafeProgram ν Λ τ ((((φ.callSource f ςs).fn).body.apply args).apply types)

section BindCallSources

variable {Λ : Library} (φ : FunDecl) (f : Fid) (ςs : Picks)

/-- The picked sources fit the parameters of the called function they are bound to
(`FunDecl.SrcsFit`), as soon as they are valid at the type constructors of those parameters and
name their type parameters in the order of the anonymous form of the constructor they produce. -/
theorem srcsFit_of_picks : ∀ (ςs : Picks) (params : List (PVar × TyConsId)),
    ςs.tyCons = params.map Prod.snd → (∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ) →
    (∀ τ ς, (τ, ς) ∈ ςs → ς.src.fn.ty.InAnonOrder) → ∀ {n : ℕ}, (∀ p ∈ params, p.2.Bounded n) →
    SrcsFit n ςs.srcs params
  | [], [], _, _, _, _, _ => List.Forall₂.nil
  | [], _ :: _, h, _, _, _, _ => by simp [tyCons] at h
  | _ :: _, [], h, _, _, _, _ => by simp [tyCons] at h
  | (τ, ς) :: ςs, p :: params, h, hv, ho, _, hb => by
    simp only [tyCons_cons, List.map_cons, List.cons.injEq] at h
    obtain ⟨hτ, h⟩ := h
    have hς := hv τ ς List.mem_cons_self
    refine List.Forall₂.cons ⟨ho τ ς List.mem_cons_self, hτ ▸ hς.src_ty.arity_eq,
      hς.typechecks.ty_bounded, hb p List.mem_cons_self⟩ (srcsFit_of_picks ςs params h
        (fun τ' ς' hm => hv τ' ς' (List.mem_cons_of_mem _ hm))
        (fun τ' ς' hm => ho τ' ς' (List.mem_cons_of_mem _ hm))
        (fun p' hp' => hb p' (List.mem_cons_of_mem _ hp')))

/-- The type constructors the picked summaries are picked for use type parameters of the called
function only. -/
theorem params_lt_of_picks (hbounded : φ.Bounded) (hcons : ςs.tyCons = φ.template.paramCons) :
    ∀ τ ς, (τ, ς) ∈ ςs → ∀ i ∈ τ.params, i < φ.tyArity := by
  intro τ ς hm i hi
  have hτ : τ ∈ ςs.tyCons := List.mem_map_of_mem (f := Prod.fst) hm
  rw [hcons] at hτ
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
  exact hbounded.param hp i hi

/-- The template binding the picked summaries around a call is structurally valid whenever the
summaries it binds are. -/
theorem callSource_valid (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ)
    (hbounded : φ.Bounded) (hcons : ςs.tyCons = φ.template.paramCons) :
    ((φ.callSource f ςs).fn).Valid :=
  (FunTempl.valid_congr (callSource_params φ f ςs _)
    (by rw [callSource_ty, Expr.bindSourcesAux_ty])).mpr
    (Expr.bindSourcesAux_spec (Λ := Λ)
    (PVar.freshen_spec (m := max (RUXt.maxNameLen φ.paramNames) ςs.maxNameLen))
    (fun i hi => Nat.lt_add_right _ (hbounded.2 i hi)) ςs.srcs φ.paramNames φ.tyArity
    (Expr.callSels φ)
    (fun types => .call f (TyArgs.tyParams types) (Term.ofVars φ.paramNames)) (TeleArg.replicate _ Ty.unit)
    (srcs_ok hvalid) (sels_eq_callSels hcons ▸ selsOk hvalid hbounded hcons) le_rfl).1

/-- The parameters of the template binding the picked summaries around a call are pairwise
distinct. -/
theorem callSource_params_nodup (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ)
    (hbounded : φ.Bounded) (hcons : ςs.tyCons = φ.template.paramCons) :
    ((φ.callSource f ςs).fn).paramNames.Nodup := by
  rw [FunTempl.paramNames_congr (callSource_params φ f ςs _)]
  exact (Expr.bindSourcesAux_spec (Λ := Λ)
    (PVar.freshen_spec (m := max (RUXt.maxNameLen φ.paramNames) ςs.maxNameLen))
    (fun i hi => Nat.lt_add_right _ (hbounded.2 i hi)) ςs.srcs φ.paramNames φ.tyArity
    (Expr.callSels φ)
    (fun types => .call f (TyArgs.tyParams types) (Term.ofVars φ.paramNames)) (TeleArg.replicate _ Ty.unit)
    (srcs_ok hvalid) (sels_eq_callSels hcons ▸ selsOk hvalid hbounded hcons) le_rfl).2.2.2.1

/-- The template binding the picked summaries around a call satisfies its specification, read
off the specification of `bindSourcesAux` (`Expr.bindSourcesAux_spec`): its parameters are those
of the latter, and so is its body as soon as the picked sources name their type parameters in
the order of the anonymous form of the constructor they produce. -/
theorem callSource_spec (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ)
    (hord : ∀ τ ς, (τ, ς) ∈ ςs → ς.src.fn.ty.InAnonOrder) (hbounded : φ.Bounded)
    (hcons : ςs.tyCons = φ.template.paramCons) (types : RUXt.TyArgs (φ.tyArity + ςs.freeArity)) :
    BindCallSourcesSpec Λ φ f ςs types := by
  have hparams := callSource_params φ f ςs
    (fun types : RUXt.TyArgs (φ.tyArity + ςs.freeArity) =>
      .call f (TyArgs.tyParams types) (Term.ofVars φ.paramNames))
  obtain ⟨-, -, hfresh, -, hsafe⟩ :=
    Expr.bindSourcesAux_spec (Λ := Λ)
    (PVar.freshen_spec (m := max (RUXt.maxNameLen φ.paramNames) ςs.maxNameLen))
    (fun i hi => Nat.lt_add_right _ (hbounded.2 i hi)) ςs.srcs φ.paramNames φ.tyArity
    (Expr.callSels φ)
    (fun types => .call f (TyArgs.tyParams types) (Term.ofVars φ.paramNames)) types
    (srcs_ok hvalid) (sels_eq_callSels hcons ▸ selsOk hvalid hbounded hcons) le_rfl
  refine ⟨callSource_valid φ f ςs hvalid hbounded hcons, ?resTy_apply_eq,
    φ.callSource_params_length f ςs (fun p hp => (hvalid p.1 p.2 hp).wellShaped),
    ?fresh, callSource_params_nodup φ f ςs hvalid hbounded hcons, ?safe⟩
  case resTy_apply_eq =>
    rw [FunTempl.resTy_apply, FunDecl.callSource_ty, FunDecl.resTy,
      FunTempl.resTy_apply, TyConsId.concretise_splitUniform_left hbounded.res]
  case fresh =>
    intro x hx
    rw [FunTempl.paramNames_congr hparams] at hx
    obtain ⟨n, y, -, rfl⟩ := hfresh x hx
    exact fun h => PVar.freshen_spec.ne_short h rfl
  case safe =>
    intro args ν τ hctx hcall
    rw [FunTempl.sig_congr hparams] at hctx
    rw [callSource_body_apply φ f ςs
      (srcsFit_of_picks ςs φ.template.params hcons hvalid hord hbounded.1)]
    refine hsafe args ν τ
      (fun s hs y hy => Picks.le_maxNameLen hs hy |>.trans (le_max_right _ _))
      (fun y hy => le_trans (RUXt.le_maxNameLen hy) (le_max_left _ _))
      ?hlen hctx ?hcall
    case hlen =>
      rw [length_srcs, FunDecl.paramNames, FunTempl.paramNames, List.length_map]
      exact le_of_eq (length_eq_of_tyCons_eq hcons).symm
    case hcall =>
      rw [← sels_eq_callSels hcons, resTys_eq_paramTypes hvalid hbounded hcons types]
      exact hcall

/-- Every parameter type of the template binding the picked summaries around a call comes from
the type arguments it is instantiated at. -/
theorem callSource_params_valid (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ)
    (hbounded : φ.Bounded) (hcons : ςs.tyCons = φ.template.paramCons)
    (types : RUXt.TyArgs (φ.tyArity + ςs.freeArity)) :
    ((φ.callSource f ςs).fn).ValidTyCons types :=
  (callSource_valid φ f ςs hvalid hbounded hcons).validTyCons types

/-- The source of the summary derived for a call typechecks: it produces the result type
constructor of the called function, at the type parameters bound for the call. -/
theorem callSource_typechecks (hmaps : Λ.MapsTo f φ) (hsafe : φ.template.safe)
    (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ)
    (hord : ∀ τ ς, (τ, ς) ∈ ςs → ς.src.fn.ty.InAnonOrder)
    (hcons : ςs.tyCons = φ.template.paramCons) :
    (φ.callSource f ςs).Typechecks Λ := by
  obtain hbounded := Λ.bounded hmaps
  obtain hdup := Λ.params_nodup hmaps
  obtain hmerge := φ.callSource_valid f ςs hvalid hbounded hcons
  obtain hdupSrcs := φ.callSource_params_nodup f ςs hvalid hbounded hcons
  refine ⟨hmerge, fun types args => ?impl⟩
  obtain hty := (callSource_spec φ f ςs hvalid hord hbounded hcons types).resTy_apply_eq
  obtain hinst := Λ.instantiates_concretise hmaps (types.splitUniform φ.tyArity ςs.freeArity).1
  refine ⟨?safe, FunDecl.callSource_safe φ f ςs, ?nodup⟩
  case nodup =>
    simp only [FunImpl.ParamsNodup, FunImpl.paramNames, FunTempl.concretise_params,
      FunTempl.sig_map_fst]
    exact hdupSrcs
  case safe =>
    simp only [FunTempl.concretise_params, FunTempl.concretise_body,
      FunTempl.concretise_ty, FunImpl.paramNames]
    refine (callSource_spec φ f ςs hvalid hord hbounded hcons types).safe args _ _ ?hctx ?hcall
    case hctx =>
      intro x τx hmem
      refine VarCtx.from_lookup_some ?_ hmem
      rw [FunTempl.sig_map_fst]
      exact hdupSrcs
    case hcall =>
      rw [hty, ← FunDecl.paramNames_concretise
          (tyargs := (types.splitUniform φ.tyArity ςs.freeArity).1),
        ← φ.concretise_ty (types.splitUniform φ.tyArity ςs.freeArity).1]
      refine safeProgram_subset (safe_call hinst hsafe) ?_
      rw [FunDecl.paramNames_concretise, FunDecl.paramTypes_concretise]
      exact VarCtx.from_subset_extend _ hdup

end BindCallSources

open scoped PFun

/-- The body of the template binding the picked summaries around a call, run on the resources
the picked summaries own, reproduces the behaviour of the call on the results of the picked
sources. -/
theorem callSource_frameStep {Λ : Library} (φ : FunDecl) (f : Fid) (ςs : Picks)
    (args : TeleArg ςs.teleOf)
    (S : SubvArgs.{0} (φ.tyArity + ςs.freeArity))
    (values : TeleArg (Tele.uniform Val ςs.valArity))
    (rvals : TeleArg (Tele.uniform Val ςs.size))
    (hF h h' : Heap) (εₛ : Exit)
    (hvalid : ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ)
    (hord : ∀ τ ς, (τ, ς) ∈ ςs → ς.src.fn.ty.InAnonOrder) (hbounded : φ.Bounded)
    (hcons : ςs.tyCons = φ.template.paramCons)
    (hdup : φ.paramNames.Nodup) (hlen : ςs.length ≤ φ.paramNames.length)
    (hdisj : hF ##ₘ h)
    (hpost : HProp h
      (PolyAsrt.at (ςs.mergeOwned Λ φ.tyArity) (args |>.app values |>.app rvals) S))
    (hstep : Λ ⊢ ⟨hF ∪ h |
      (Expr.call f (S.tys.splitUniform φ.tyArity ςs.freeArity).1.toList
        (Term.ofVars φ.paramNames)).substs φ.paramNames
        (Term.ofVals ((ςs.mergeVals Λ φ.tyArity S).at
        (args |>.app values |>.app rvals)))⟩ ⇓ᵢ ⟨h' | εₛ⟩) :
    ∃ hp, HProp hp (((φ.callSource f ςs).fn).ownVals (fun C => C.ownsAt Λ S)
        values.toList)
      ∧ hF ##ₘ hp
      ∧ Λ ⊢ ⟨hF ∪ hp | ((((φ.callSource f ςs).fn).body.apply args).apply S.tys).substs
          ((φ.callSource f ςs).fn).paramNames (Term.ofVals values.toList)⟩
          ⇓ᵢ ⟨h' | εₛ⟩ := by
  /- The sources of the picked summaries are run on the input values of the call, transported
  along the equality between the number of input values the summaries declare and the number
  of parameters their templates have. -/
  set values' : TeleArg (Tele.uniform Val (Source.mergedValArity ςs.srcs)) :=
    (mergedValArity_srcs ςs (fun p hp => (hvalid p.1 p.2 hp).wellShaped)).symm ▸ values
    with hvalues'
  have hv : values.toList = values'.toList := by
    rw [hvalues', TeleArg.toList_transport]
  obtain ⟨g, hruns⟩ :=
    mergeOwned_runs ςs φ.tyArity args S values values' rvals h hv hvalid hord
      (params_lt_of_picks φ ςs hbounded hcons) hpost
  rw [sels_eq_callSels hcons] at hruns
  obtain ⟨hpre, hdisjg, hchain⟩ := Expr.bindSourcesAux_frameStep
    (PVar.freshen_spec (m := max (RUXt.maxNameLen φ.paramNames) ςs.maxNameLen))
    (fun i hi => Nat.lt_add_right _ (hbounded.2 i hi)) ςs.srcs φ.paramNames (fun _ => 0)
    φ.tyArity (Expr.callSels φ)
    (fun types => .call f (TyArgs.tyParams types) (Term.ofVars φ.paramNames))
    args S.tys values' _ g hF h h' εₛ (srcs_ok hvalid)
    (fun s hs y hy => le_trans (Picks.le_maxNameLen hs hy) (le_max_right _ _))
    (fun y hy => le_trans (RUXt.le_maxNameLen hy) (le_max_left _ _))
    hdup (by rw [length_srcs]; exact hlen)
    (fun ts t ht => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
      exact le_trans (RUXt.le_maxNameLen hy) (le_max_left _ _))
    (sels_eq_callSels hcons ▸ selsOk hvalid hbounded hcons) le_rfl
    hdisj hruns hstep
  rw [← hv] at hpre hchain
  have hparams := callSource_params φ f ςs
    (fun types : RUXt.TyArgs (φ.tyArity + ςs.freeArity) =>
      .call f (TyArgs.tyParams types) (Term.ofVars φ.paramNames))
  refine ⟨g, ?_, hdisjg, ?_⟩
  · rw [FunTempl.ownVals, FunTempl.paramCons_congr hparams]
    exact hpre
  · rw [callSource_body_apply φ f ςs (srcsFit_of_picks ςs φ.template.params hcons hvalid hord hbounded.1),
      FunTempl.paramNames_congr hparams]
    exact hchain

end FunDecl

/-! ### Properties of safe picks -/

namespace FunDecl

variable {φ : FunDecl} {S : SummCtx} {ςs : Picks}

/-- Safety of picks is decidable as soon as membership in the type space is. -/
instance decidableSafePicks (φ : FunDecl) (S : SummCtx) (ςs : Picks)
    [∀ τ ς, Decidable (S.MemTy τ ς)] : Decidable (φ.SafePicks S ςs) := by
  unfold SafePicks; infer_instance

/-- The type constructors the picked summaries are picked for are the type constructors of
the parameters of the called function. -/
theorem SafePicks.tyCons_eq (h : φ.SafePicks S ςs) : ςs.tyCons = φ.template.paramCons := h.1
/-- Every picked summary is a summary of the type space it is picked from, for the type
constructor it is picked for. -/
theorem SafePicks.mem (h : φ.SafePicks S ςs) : ∀ τ ς, (τ, ς) ∈ ςs → S.MemTy τ ς :=
  fun _ _ hp => h.2 _ hp
/-- The picked summaries of a valid type space are valid at the type constructors they are
picked for. -/
theorem SafePicks.valid {Λ : Library} (h : φ.SafePicks S ςs) (hsumm : S.Valid Λ) :
    ∀ τ ς, (τ, ς) ∈ ςs → ς.Valid Λ τ :=
  fun τ ς hp => hsumm τ ς (h.mem τ ς hp)

end FunDecl

/-! ### Properties of sources -/

theorem source_params_valid {Λ : Library} {S : SummCtx} {ςs : Picks}
    (f : Fid) (φ : FunDecl)
    (hbounded : φ.Bounded)
    (hsumm : SummCtx.Valid Λ S) (hpicks : φ.SafePicks S ςs) :
    ∀ types x τ, (x, τ) ∈ ((φ.callSource f ςs).fn).sig.apply types → τ ∈ types.toList :=
  fun types => φ.callSource_params_valid _ _
    (hpicks.valid hsumm) hbounded hpicks.tyCons_eq types

theorem source_reachable {L : Logic.{0}} (hL : L.Sound) {Λ : Library} {S : SummCtx}
    {ςs : Picks} {f : Fid} {φ : FunDecl} (hmaps : Λ.MapsTo f φ) (hsafe : φ.template.safe)
    (hsumm : SummCtx.Valid Λ S) (hordS : ∀ τ ς, S.MemTy τ ς → ς.src.fn.ty.InAnonOrder)
    (hpicks : φ.SafePicks S ςs)
    {ε : LExit} {Ψ : ςs.DerivedPost φ.tyArity} {Ψ' : φ.Subvariant ςs}
    (hcall : ςs.DerivableCall L Λ f ε Ψ)
    (hequiv : Ψ.SimplifiesTo semSolver Ψ') :
    (φ.summary f ςs Ψ').Reachable Λ φ.template.ty ε := by
  obtain hbounded := Λ.bounded hmaps
  obtain hcons := hpicks.tyCons_eq
  obtain hvalid := hpicks.valid hsumm
  have hord : ∀ τ ς, (τ, ς) ∈ ςs → ς.src.fn.ty.InAnonOrder :=
    fun τ ς hp => hordS τ ς (hpicks.mem τ ς hp)
  obtain hdup := Λ.params_nodup hmaps
  have hlenγ : ςs.length = φ.paramNames.length := by
    rw [FunDecl.paramNames, FunTempl.paramNames, List.length_map]
    exact (Picks.length_eq_of_tyCons_eq hcons).symm
  refine ⟨(FunDecl.callSource_ty φ f ςs) ▸ TyConsId.Match.refl _,
    φ.callSource_typechecks f ςs hmaps hsafe hvalid hord hcons, ?triple⟩
  case triple =>
    refine Summary.uxFrameTriple_triple_iff.mpr fun args Ss r h' hΦ => ?_
    have hux := uxTriple_poly.mp (hcall.uxFrameTriple hL)
    rw [Summary.post_apply] at hΦ
    obtain ⟨rvals, hΨ⟩ := (hequiv.ownedAt (f := f) r args Ss h').mp hΦ
    set args' : TeleArg (ςs.teleOf.app (Tele.uniform Val ςs.valArity)) := args with hargs'
    have hfst : args'.fst = args.fst := rfl
    have hsnd : args'.snd.toList = args.snd.toList := rfl
    obtain ⟨h, hpost, εₛ, hε, hstep⟩ := hux _ Ss r h' hΨ
    rw [Picks.mergeCall_eq, Picks.mergeTys, teleLift_at] at hstep
    simp only [TyArgs.tyParams] at hstep
    have hstep' : Λ ⊢ ⟨∅ ∪ h |
        (Expr.call f ((SubvArgs.tys Ss).splitUniform φ.tyArity ςs.freeArity).1.toList
            (Term.ofVars φ.paramNames)).substs φ.paramNames
          (Term.ofVals ((ςs.mergeVals Λ φ.tyArity Ss).at (args'.app rvals)))⟩ ⇓ᵢ ⟨h' | εₛ⟩ := by
      rw [PFun.empty_union, Expr.substs_call
        (by rw [Picks.mergeVals_length]; exact hlenγ.symm) hdup]
      exact hstep
    obtain ⟨hp, hpre, -, hchain⟩ := FunDecl.callSource_frameStep φ f ςs
      args'.fst Ss args'.snd rvals ∅ h h' εₛ hvalid hord hbounded hcons hdup
      (le_of_eq hlenγ) (PFun.disjoint_empty_left _)
      (by simpa only [TeleArg.app_fst_snd] using hpost)
      (by simpa only [TeleArg.app_fst_snd] using hstep')
    rw [PFun.empty_union] at hchain
    simp only [hfst, hsnd] at hpre hchain
    exact ⟨hp, (Summary.pre_apply_ownVals _ _ _ _).symm ▸ hpre, εₛ, hε,
      (Summary.expr_apply _ _ _).symm ▸ hchain⟩

end RUXt
