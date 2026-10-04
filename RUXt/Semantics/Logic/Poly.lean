import RUXt.Semantics.Logic.Basic

/-!
# Typed subvariants and the triples parametric on them

Properties of typed subvariants and of their tuples, the poly program and triple builders, and
the under-approximate semantics of a triple parametric on typed subvariants read at every tuple
of symbolic values and every tuple of typed subvariants (`uxTriple_poly`).
-/

namespace RUXt

universe u v

/-! ## Properties

### Ownership through a typed subvariant -/

namespace TypedSubvariants

@[simp] theorem get_mk_nil (Λ : Library) (τ : Ty) (i : ℕ) (v : Val) :
    get ⟨τ, []⟩ Λ i v = (.opaque Λ τ v : Asrt.{u}) := by
  rw [get]
  rfl
@[simp] theorem get_mk_cons_succ (Λ : Library) (τ : Ty)
    (s : Val → Asrt.{u}) (l : List (Val → Asrt.{u})) (i : ℕ) (v : Val) :
    get ⟨τ, s :: l⟩ Λ (i + 1) v = get ⟨τ, l⟩ Λ i v := rfl

/-- Reading a subvariant that the list does provide. -/
theorem get_of_getElem? {ts : TypedSubvariants.{u}} {Λ : Library}
    {i : ℕ} {s : Val → Asrt.{u}} (h : ts.own[i]? = some s) (v : Val) :
    ts.get Λ i v = s v := by
  rw [get, h]

end TypedSubvariants

namespace SubvArgs

variable {m n : ℕ}

/-- Transport a tuple along an equality of arities. -/
def transport (h : m = n) (S : SubvArgs.{u} m) : SubvArgs.{u} n := h ▸ S

/-- Reading a component off a tuple, by position in its list. -/
theorem get_eq_getElem {S : SubvArgs.{u} n} {i : ℕ} (h : i < n) :
    get S i = S.toList[i]'(by rw [TeleArg.toList_length]; exact h) := by
  rw [get, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [TeleArg.toList_length]; exact h), Option.getD_some]

/-- Two tuples with the same components are the same tuple. -/
theorem ext {S T : SubvArgs.{u} n} (h : ∀ i < n, get S i = get T i) : S = T := by
  refine TeleArg.toList_injective _ _ (List.ext_getElem (by simp) fun i hi hi' => ?_)
  rw [TeleArg.toList_length] at hi
  rw [← get_eq_getElem hi, ← get_eq_getElem hi, h i hi]

@[simp] theorem toList_tys (S : SubvArgs.{u} n) :
    S.tys.toList = S.toList.map TypedSubvariants.ty :=
  TeleArg.toList_mapUniform _ S

@[simp] theorem get_tys (S : SubvArgs.{u} n) (i : ℕ) : S.tys.get i = (S.get i).ty := by
  rw [TyArgs.get, get, toList_tys, List.getD, List.getD, List.getElem?_map]
  cases S.toList[i]? <;> rfl

/-- The types of the tuple of typed subvariants of a tuple of types are those types. -/
@[simp] theorem tys_ofTys : ∀ {n : ℕ} (T : TyArgs n), (ofTys.{u} T).tys = T
  | 0, _ => rfl
  | _ + 1, ⟨τ, T⟩ => congrArg (Sigma.mk τ) (tys_ofTys T)

/-- Reading a component off the first part of a split tuple (`TeleArg.splitUniform`). -/
theorem get_splitUniform_left {n m : ℕ} (a : SubvArgs.{u} (n + m)) {j : ℕ}
    (hj : j < n) : get (a.splitUniform n m).1 j = a.get j :=
  TeleArg.getD_toList_splitUniform_left default a hj

/-- Reading a component off the second part of a split tuple (`TeleArg.splitUniform`). -/
theorem get_splitUniform_right {n m : ℕ} (a : SubvArgs.{u} (n + m)) (j : ℕ) :
    get (a.splitUniform n m).2 j = a.get (n + j) := by
  simp only [get, TeleArg.toList_splitUniform_right, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

@[simp] theorem toList_transport (h : m = n) (S : SubvArgs.{u} m) :
    (transport h S).toList = S.toList := TeleArg.toList_transport h S

@[simp] theorem toList_reindex (ρ : ℕ → ℕ) (n : ℕ) (S : SubvArgs.{u} m) :
    (S.reindex default ρ n).toList = (List.range n).map fun i => S.get (ρ i) :=
  TeleArg.toList_reindex _ _ _ _

@[simp] theorem get_reindex {ρ : ℕ → ℕ} {n : ℕ} {S : SubvArgs.{u} m} {i : ℕ} (h : i < n) :
    get (S.reindex default ρ n) i = S.get (ρ i) :=
  TeleArg.getD_toList_reindex _ _ _ h

/-- Forgetting the assertions commutes with reindexing. -/
@[simp] theorem tys_reindex (ρ : ℕ → ℕ) (n : ℕ) (S : SubvArgs.{u} m) :
    SubvArgs.tys (TeleArg.reindex default ρ n S) = S.tys.reindex .unit ρ n := by
  refine TeleArg.toList_injective _ _ ?_
  rw [toList_tys, toList_reindex, TyArgs.toList_reindex, List.map_map]
  exact List.map_congr_left fun i _ => (get_tys S (ρ i)).symm

/-- Every component of a constant tuple is that constant. -/
theorem get_replicate {n i : ℕ} (ts : TypedSubvariants.{u}) (h : i < n) :
    get (TeleArg.replicate n ts : SubvArgs.{u} n) i = ts := by
  rw [get, TeleArg.replicate_toList, List.getD_eq_getElem?_getD,
    List.getElem?_replicate_of_lt h, Option.getD_some]

/-- The type arguments of a constant tuple of typed subvariants. -/
@[simp] theorem tys_replicate (n : ℕ) (ts : TypedSubvariants.{u}) :
    tys (TeleArg.replicate n ts : SubvArgs.{u} n) = TeleArg.replicate n ts.ty :=
  TeleArg.mapUniform_replicate _ ts n

/-- Forgetting the assertions commutes with transport. -/
@[simp] theorem tys_transport (h : m = n) (S : SubvArgs.{u} m) :
    (transport h S).tys = TyArgs.transport h S.tys := by
  subst h; rfl

end SubvArgs

/-! ### Triples parametric on typed subvariants -/

/-- The expression a poly program runs at a tuple of symbolic values and a tuple of typed
subvariants. -/
def PolyExpr.at {n : ℕ} {tt : Tele.{u}} (e : PolyExpr n tt) (args : TeleArg tt)
    (S : SubvArgs.{u} n) : Expr :=
  TeleFun.at e ((TeleArg.uliftArg args).app S)

/-- The triple parametric on `n` typed subvariants assembled from ordinary functions of the
symbolic values and of the typed subvariants. -/
def polyTriple {n : ℕ} {tt : Tele.{u}} (P : TeleArg tt → SubvArgs.{u} n → Asrt.{u})
    (e : TeleArg tt → SubvArgs.{u} n → Expr) (ε : LExit)
    (Q : Val → TeleArg tt → SubvArgs.{u} n → Asrt.{u}) : SymTriple (polyTele.{u} n tt) :=
  ⟨polyAsrt P, polyExpr e, ε, fun r => polyAsrt (Q r)⟩

/-- The assertion a poly assertion built from an ordinary function gives at a tuple of
symbolic values and a tuple of typed subvariants. -/
@[simp] theorem polyAsrt_at {n : ℕ} {tt : Tele.{u}}
    (F : TeleArg tt → SubvArgs.{u} n → Asrt.{u}) (args : TeleArg tt) (S : SubvArgs.{u} n) :
    (polyAsrt F).at args S = F args S := by
  rw [PolyAsrt.at, polyAsrt, teleBind_apply, TeleArg.fst_append,
    TeleArg.snd_append, TeleArg.ulower_uliftArg]

/-- A poly assertion built from an ordinary function, applied to a tuple of the poly
telescope: the symbolic values and the typed subvariants are read off that tuple. -/
@[simp] theorem polyAsrt_apply {n : ℕ} {tt : Tele.{u}}
    (F : TeleArg tt → SubvArgs.{u} n → Asrt.{u}) (a : TeleArg (polyTele.{u} n tt)) :
    TeleFun.apply (polyAsrt F) a = F a.fst.ulower a.snd :=
  teleBind_apply _ a

/-- The program a poly program built from an ordinary function runs at a tuple of symbolic
values and a tuple of typed subvariants. -/
@[simp] theorem polyExpr_at {n : ℕ} {tt : Tele.{u}}
    (e : TeleArg tt → SubvArgs.{u} n → Expr) (args : TeleArg tt) (S : SubvArgs.{u} n) :
    (polyExpr e).at args S = e args S := by
  rw [PolyExpr.at, polyExpr, teleLift_at, TeleArg.fst_append, TeleArg.snd_append,
    TeleArg.ulower_uliftArg]

/-- Every argument tuple of a poly telescope is a tuple of symbolic values followed by a
tuple of typed subvariants. -/
@[simp] theorem polyTele_arg_eq {n : ℕ} {tt : Tele.{u}} (a : TeleArg (polyTele.{u} n tt)) :
    (TeleArg.uliftArg a.fst.ulower).app a.snd = a := by
  rw [TeleArg.uliftArg_ulower, TeleArg.app_fst_snd]

/-- Reading a component of a triple parametric on typed subvariants at a tuple of symbolic
values and a tuple of typed subvariants is applying it to the two of them, appended. -/
theorem PolyAsrt.at_eq_apply {n : ℕ} {tt : Tele.{u}} (P : PolyAsrt.{u} n tt)
    (args : TeleArg tt) (S : SubvArgs.{u} n) :
    P.at args S = TeleFun.apply P ((TeleArg.uliftArg args).app S) := rfl

/-- The under-approximate semantics of a triple parametric on typed subvariants holds exactly
when it holds at every tuple of symbolic values and every tuple of typed subvariants. -/
theorem uxTriple_poly {n : ℕ} {tt : Tele.{u}}
    {step : Library → Heap → Expr → Heap → Exit → Prop} {Λ : Library}
    {T : SymTriple.{u} (polyTele.{u} n tt)} :
    UXTriple step Λ T ↔
      ∀ (args : TeleArg tt) (S : SubvArgs.{u} n) (v : Val) (h' : Heap),
        HProp h' (PolyAsrt.at (T.2.2.2 v) args S) →
          ∃ h, HProp h (PolyAsrt.at T.1 args S) ∧
            ∃ εₛ, T.2.2.1.toExit v = some εₛ ∧ step Λ h (PolyExpr.at T.2.1 args S) h' εₛ := by
  obtain ⟨P, e, ε, Q⟩ := T
  constructor
  · intro h args S v h' hQ
    exact h ((TeleArg.uliftArg args).app S) v h' hQ
  · intro h a v h' hQ
    rw [← polyTele_arg_eq a] at hQ ⊢
    exact h a.fst.ulower a.snd v h' hQ

/-- The under-approximate semantics of a triple parametric on typed subvariants assembled
from ordinary functions. -/
theorem uxTriple_polyTriple {n : ℕ} {tt : Tele.{u}}
    {step : Library → Heap → Expr → Heap → Exit → Prop} {Λ : Library}
    {P : TeleArg tt → SubvArgs.{u} n → Asrt.{u}} {e : TeleArg tt → SubvArgs.{u} n → Expr}
    {ε : LExit} {Q : Val → TeleArg tt → SubvArgs.{u} n → Asrt.{u}} :
    UXTriple step Λ (polyTriple P e ε Q) ↔
      ∀ (args : TeleArg tt) (S : SubvArgs.{u} n) (v : Val) (h' : Heap),
        HProp h' (Q v args S) →
          ∃ h, HProp h (P args S) ∧
            ∃ εₛ, ε.toExit v = some εₛ ∧ step Λ h (e args S) h' εₛ := by
  rw [uxTriple_poly]
  simp only [polyTriple, polyAsrt_at, polyExpr_at]

end RUXt
