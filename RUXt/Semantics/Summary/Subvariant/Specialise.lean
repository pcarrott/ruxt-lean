import RUXt.Model.Summary.Specialise
import RUXt.Semantics.Summary.Subvariant.Basic

/-!
# The semantics of the specialisation of a subvariant

Properties of `Subvariant.specialise`, which inserts the typed subvariant describing the
pinned type at the pinned position: the tuple operations involved
(`TeleArg.mapUniform_insertUniform` and friends), the types a specialised subvariant hands to
the subvariant it specialises (`SubvArgs.tys_insertUniformPred_of_get`), the resources a type
parameter of a specialised source describes (`TyConsId.ownsAt_param_substCons_specSubst`), and
the reading of a specialised subvariant (`Subvariant.specialise_at`).
-/

namespace RUXt

universe u v

/-- Mapping a function over a tuple with an extra argument inserted. -/
theorem TeleArg.mapUniform_insertUniform {X : Type u} {Y : Type v} (f : X → Y) (x : X) :
    ∀ (j n : ℕ) (a : TeleArg (Tele.uniform X n)),
      (TeleArg.insertUniform x j a).mapUniform f
        = TeleArg.insertUniform (f x) j (a.mapUniform f)
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | j + 1, n + 1, a => by
      show (⟨f a.1, (TeleArg.insertUniform x j a.2).mapUniform f⟩ :
          TeleArg (Tele.uniform Y (n + 1 + 1)))
        = ⟨f a.1, TeleArg.insertUniform (f x) j (a.2.mapUniform f)⟩
      rw [mapUniform_insertUniform f x j n a.2]

/-- Mapping a function over a tuple with an extra argument inserted, at length `n - 1`. -/
theorem TeleArg.mapUniform_insertUniformPred {X : Type u} {Y : Type v} (f : X → Y) (x : X)
    (j : ℕ) :
    ∀ (n : ℕ) (a : TeleArg (Tele.uniform X (n - 1))),
      (TeleArg.insertUniformPred x j (n := n) a).mapUniform f
        = TeleArg.insertUniformPred (f x) j (n := n) (a.mapUniform f)
  | 0, _ => rfl
  | _ + 1, a => TeleArg.mapUniform_insertUniform f x j _ a

/-- The type arguments a specialised subvariant hands to the subvariant it specialises: the
type arguments it keeps — read off `T` along `ρ` — with the pinned type inserted at the pinned
position. -/
theorem SubvArgs.tys_insertUniformPred_of_get {n K : ℕ} (x : TypedSubvariants.{0})
    (T : SubvArgs.{0} K) (T' : SubvArgs.{0} (n - 1)) (ρ : ℕ → ℕ)
    (hT : ∀ k < n - 1, T'.get k = T.get (ρ k)) (j : ℕ) :
    SubvArgs.tys (TeleArg.insertUniformPred x j (n := n) T')
      = TeleArg.insertUniformPred x.ty j (n := n) (TeleArg.reindex Ty.unit ρ (n - 1) (SubvArgs.tys T)) := by
  rw [SubvArgs.tys, TeleArg.mapUniform_insertUniformPred]
  refine congrArg _ (TyArgs.ext fun k hk => ?_)
  rw [TyArgs.get_reindex hk, ← SubvArgs.tys, SubvArgs.get_tys, SubvArgs.get_tys, hT k hk]

/-- Reading a component off a block of a tuple. -/
@[simp] theorem SubvArgs.get_block {n : ℕ} (S : SubvArgs.{0} n) (start : ℕ) {len j : ℕ}
    (hj : j < len) : SubvArgs.get (S.block default start len : SubvArgs.{0} len) j
      = S.get (start + j) :=
  TeleArg.getD_toList_block _ S start hj

/-- Arranging the blocks of the typed subvariant arguments of a specialised summary in the order
of the type parameters of the summary it specialises — the first `i`, the pinned typed
subvariant `x`, then the `n - 1 - i` following the `k` type parameters of the pinned
constructor — inserts `x` at position `i` among the kept typed subvariants, read off at their
positions in the specialised summary (`TyConsId.keptIdx`). -/
theorem SubvArgs.arrange_eq_insertUniformPred {n N : ℕ} (S : SubvArgs.{0} N)
    (x : TypedSubvariants.{0}) {i : ℕ} (k : ℕ) (hi : i < n) :
    ((S.block default 0 i).appendUniform ((S.block default (i + k) (n - 1 - i)).consUniform x)
        |>.reindex default id n : SubvArgs.{0} n)
      = TeleArg.insertUniformPred x i (n := n)
          (TeleArg.reindex default (TyConsId.keptIdx i k) (n - 1) S) := by
  refine SubvArgs.ext fun j hj => ?_
  rw [SubvArgs.get, TeleArg.getD_toList_arrange _ S x k hi j, SubvArgs.get,
    TeleArg.getD_toList_insertUniformPred _ _ i hi _ j]
  by_cases hji : j = i
  · rw [if_pos hji, if_pos hji]
  · rw [if_neg hji, if_neg hji, if_pos hj]
    by_cases hlt : j < i
    · rw [if_pos hlt, if_pos hlt]
      show S.get j = SubvArgs.get (TeleArg.reindex default (TyConsId.keptIdx i k) (n - 1) S) j
      rw [SubvArgs.get_reindex (by omega), TyConsId.keptIdx, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt]
      show S.get (j - 1 + k) = SubvArgs.get (TeleArg.reindex default (TyConsId.keptIdx i k) (n - 1) S) (j - 1)
      rw [SubvArgs.get_reindex (by omega), TyConsId.keptIdx, if_neg (by omega)]

/-- The resources a type parameter of a specialised source describes are the ones the type
parameter it came from describes, at the typed subvariant arguments of the specialised source —
the kept ones, `S'`, read off `S` at their positions (`TyConsId.keptIdx`) — with the typed
subvariant of the pinned parameter inserted at its position. -/
theorem TyConsId.ownsAt_param_substCons_specSubst (Λ : Library) {n K : ℕ} {i j : TyIdx}
    (hi : i < n) (hj : j < n) (hji : j ≠ i) (τ : TyConsId) (ts : TypedSubvariants.{0})
    (S : SubvArgs.{0} K) (S' : SubvArgs.{0} (n - 1))
    (hS : ∀ k < n - 1, S'.get k = S.get (TyConsId.keptIdx i τ.arity k))
    (g : ℕ) (v : Val) :
    ((TyConsId.param j).substCons (TyConsId.specSubst i τ)).ownsAt Λ S g v
      = (TyConsId.param j).ownsAt Λ (TeleArg.insertUniformPred ts i (n := n) S') g v := by
  have key : ∀ a b c : Nat, a < c → b < c → b ≠ a → (if b < a then b else b - 1) < c - 1 := by
    intro a b c h1 h2 h3
    split <;> omega
  have hj' : (if j < i then j else j - 1) < n - 1 := key i j n hi hj hji
  have hget : SubvArgs.get (TeleArg.insertUniformPred ts i (n := n) S') j
      = S.get (TyConsId.keptIdx i τ.arity (if j < i then j else j - 1)) := by
    rw [SubvArgs.get, TeleArg.getD_toList_insertUniformPred _ _ i hi _ j, if_neg hji,
      ← SubvArgs.get, hS _ hj']
  rw [TyConsId.substCons_param, TyConsId.specSubst, if_neg hji, TyConsId.ownsAt_param,
    TyConsId.ownsAt_param, hget]

/-- A type constructor `τ` in anonymous form, instantiated at typed subvariants `T` reading the
`τ.arity` typed subvariant arguments starting at `k`, is `τ` shifted to `k`
(`TyConsId.shiftTo`) and concretised at the whole tuple. -/
theorem TyConsId.instantiate_tys_of_get {τ : TyConsId} (hτ : τ.anon = τ) {k N : ℕ}
    (S : SubvArgs.{0} N) (T : SubvArgs.{0} τ.arity)
    (hT : ∀ j < τ.arity, T.get j = S.get (k + j)) :
    (τ.instantiate (SubvArgs.tys T).toList).getD Ty.unit
      = (τ.shiftTo k).concretise S.tys := by
  have hbd : τ.Bounded τ.arity := by
    have := TyConsId.anon_bounded τ; rwa [hτ] at this
  have hb : τ.Bounded (SubvArgs.tys T).toList.length := by
    rw [TeleArg.toList_length]; exact hbd
  rw [TyConsId.instantiate_eq_some hb, Option.getD_some, TyConsId.concretise, TyConsId.concretise,
    TyConsId.shiftTo, hτ, TyConsId.subst_rename]
  refine TyConsId.subst_congr τ fun j hj => ?_
  rw [TyArgs.get_ofList, Function.comp_apply, ← TyArgs.get, SubvArgs.get_tys, SubvArgs.get_tys,
    hT j (hbd j hj)]

/-- The body of a specialised subvariant (`Subvariant.specialise`), read at a result value
`r`, a tuple of general arguments and a tuple of typed subvariant arguments of the specialised
subvariant, *and* at a list `rs` of values the let-bound sources are taken to produce: the
postcondition `Φ` at the input values it keeps with `rs` woven in at the pinned parameters
(`weaveVals`), and at the blocks of `S` arranged in the order of its type parameters, with the
pinned typed subvariant at position `i`. -/
def Subvariant.specialiseAt (Φ : Subvariant) (ps : List (PVar × TyConsId)) (i : TyIdx)
    (τ : TyConsId) (ςs : List Summary) (r : Val)
    (args : TeleArg (Φ.specialise ps i τ ςs).genTele)
    (S : SubvArgs.{0} (Φ.specialise ps i τ ςs).arity) (rs : List Val) : Asrt.{0} :=
  let ⟨kept, vals⟩ := args.snd.splitUniform (Φ.valArity - ςs.length) _
  let ownVals := .ofListPad .unit Φ.valArity (weaveVals i kept.toList rs ps)
  let subvs :=
    let pinnedSubv :=
      let ⟨subvs, free⟩ : SubvArgs τ.arity × SubvArgs _ :=
        (S.block default i τ.arity, S.block default (Φ.arity - 1 + τ.arity) _)
      ⟨τ.instantiate subvs.tys.toList |>.getD .unit,
        subvs.ownAssertions ςs free args.fst.snd vals⟩
    let ⟨before, after⟩ :=
      (S.block default 0 i, S.block default (i + τ.arity) (Φ.arity - 1 - i))
    (before.appendUniform (after.consUniform pinnedSubv)).reindex default id Φ.arity
  (Φ.asrt r).at (args.fst.fst.app ownVals) subvs

/-- A specialised subvariant (`Subvariant.specialise`), read at a result value, a tuple of
general arguments and a tuple of typed subvariant arguments: for some list `rs` of values the
let-bound sources produce, the reading `Subvariant.specialiseAt`. -/
theorem Subvariant.specialise_at (Φ : Subvariant) (ps : List (PVar × TyConsId)) (i : TyIdx)
    (τ : TyConsId) (ςs : List Summary) (r : Val)
    (args : TeleArg (Φ.specialise ps i τ ςs).genTele)
    (S : SubvArgs.{0} (Φ.specialise ps i τ ςs).arity) :
    ((Φ.specialise ps i τ ςs).asrt r).at args S
      = .ex fun rs : List Val => Φ.specialiseAt ps i τ ςs r args S rs := by
  dsimp only [Subvariant.specialise]
  exact polyAsrt_at _ args S

end RUXt
