import Mathlib.Data.Set.Insert
import RUXt.Lang.Types.Basic

namespace RUXt

/-! ### Memory locations -/

/-- Memory blocks. -/
abbrev Block := ℕ
/-- Memory locations: a block together with an offset into it. -/
abbrev Loc := Block × ℕ
/-- `offset l i` shifts the location `l` by `i` cells (`l +ₗ i`). -/
def Loc.offset : Loc → ℕ → Loc | ⟨b, i⟩, n => (b, i + n)
@[inherit_doc] scoped infixl:65 " +ₗ " => Loc.offset

/-! ### Language syntax -/

/-- Program variables -/
abbrev PVar := String
/-- Binders: anonymous or named. -/
inductive Binder
  | anon
  | named (x : PVar)
deriving DecidableEq

/-- Language values. -/
inductive Val
  | int (z : ℤ)
  | bool (b : Bool)
  | loc (l : Loc)
  | unit
deriving DecidableEq
/-- Language terms. -/
inductive Term
  | var (x : PVar)
  | val (v : Val)
deriving DecidableEq

/-- Unary operations. -/
inductive UnOp
  | minus
  | not
deriving DecidableEq
/-- Binary operations. -/
inductive BinOp
  | add
  | mod
  | eq
  | lt
  | offset
deriving DecidableEq
/-- Pure expressions. -/
inductive Pure
  | term (t : Term)
  | unOp (op : UnOp) (p : Pure)
  | binOp (op : BinOp) (p₁ p₂ : Pure)
deriving DecidableEq

/-- Function identifiers. -/
abbrev Fid := String
/-- Program expressions. -/
inductive Expr
  | pure (p : Pure)
  | error
  | assume (t : Term)
  | letIn (x : Binder) (e₁ e₂ : Expr)
  | choice (e₁ e₂ : Expr)
  | alloc (t : Term)
  | free (t : Term)
  | store (t₁ t₂ : Term)
  | load (t : Term)
  | call (f : Fid) (τs : List Ty) (ts : List Term)

/-! ### Syntactic sugar -/

namespace Term

abbrev int (z : ℤ) : Term := .val (.int z)
abbrev bool (b : Bool) : Term := .val (.bool b)
abbrev true : Term := .bool Bool.true
abbrev false : Term := .bool Bool.false
abbrev loc (l : Loc) : Term := .val (.loc l)
abbrev unit : Term := .val .unit

/-- A list of values as terms. -/
def ofVals (vs : List Val) : List Term := vs.map .val
/-- A list of variables as terms. -/
def ofVars (xs : List PVar) : List Term := xs.map .var

end Term

namespace Pure

abbrev val (v : Val) : Pure := .term (.val v)
abbrev var (x : PVar) : Pure := .term (.var x)
abbrev int (z : ℤ) : Pure := .term (.int z)
abbrev bool (b : Bool) : Pure := .term (.bool b)
abbrev true : Pure := .term .true
abbrev false : Pure := .term .false
abbrev loc (l : Loc) : Pure := .term (.loc l)
abbrev unit : Pure := .term .unit
abbrev minus (p : Pure) : Pure := .unOp .minus p
abbrev not (p : Pure) : Pure := .unOp .not p
abbrev add (p₁ p₂ : Pure) : Pure := .binOp .add p₁ p₂
abbrev mod (p₁ p₂ : Pure) : Pure := .binOp .mod p₁ p₂
abbrev eq (p₁ p₂ : Pure) : Pure := .binOp .eq p₁ p₂
abbrev lt (p₁ p₂ : Pure) : Pure := .binOp .lt p₁ p₂
abbrev offset (p₁ p₂ : Pure) : Pure := .binOp .offset p₁ p₂

end Pure

namespace Expr

abbrev val (v : Val) : Expr := .pure (.val v)
abbrev var (x : PVar) : Expr := .pure (.var x)
abbrev int (z : ℤ) : Expr := .pure (.int z)
abbrev bool (b : Bool) : Expr := .pure (.bool b)
abbrev true : Expr := .pure .true
abbrev false : Expr := .pure .false
abbrev loc (l : Loc) : Expr := .pure (.loc l)
abbrev unit : Expr := .pure .unit

/-- A list of values as the expressions producing them. -/
def ofVals (vs : List Val) : List Expr := vs.map .val

end Expr

/-! ### Evaluation -/

/-- Term evaluation (`⌊ t ⌋ₜ`). -/
def Term.eval : Term → Option Val
  | .var _ => none
  | .val v => some v

/-- Evaluation of unary operations. -/
def UnOp.eval : UnOp → Val → Option Val
  | .minus, .int z => some (.int (-z))
  | .not, .bool b => some (.bool !b)
  | _, _ => none

/-- Evaluation of binary operations. -/
def BinOp.eval : BinOp → Val → Val → Option Val
  | .add, .int z₁, .int z₂ => some (.int (z₁ + z₂))
  | .mod, .int z₁, .int z₂ => some (.int (z₁.tmod z₂))
  | .eq, v₁, v₂ => some (.bool (decide (v₁ = v₂)))
  | .lt, .int z₁, .int z₂ => some (.bool (decide (z₁ < z₂)))
  | .offset, .loc l, .int z => some (.loc (l +ₗ z.toNat))
  | _, _, _ => none

/-- Evaluation of pure expressions (`⌊ p ⌋ₚ`). -/
def Pure.eval : Pure → Option Val
  | .term t => t.eval
  | .unOp op p =>
      match p.eval with
      | some v => op.eval v
      | none => none
  | .binOp op p₁ p₂ =>
      match p₁.eval, p₂.eval with
      | some v₁, some v₂ => op.eval v₁ v₂
      | _, _ => none

/-! ### Substitution and closed expressions -/

def Term.Closed (X : Set PVar) : Term → Prop
  | .var x => x ∈ X
  | .val _ => True

def Term.subst (T : Term) (x : PVar) (t : Term) : Term :=
  if T = .var x then t else T

def Pure.Closed (X : Set PVar) : Pure → Prop
  | .term t => t.Closed X
  | .unOp _ p => p.Closed X
  | .binOp _ p₁ p₂ => p₁.Closed X ∧ p₂.Closed X

def Pure.subst (p : Pure) (x : PVar) (t : Term) : Pure :=
  match p with
  | .term T => .term (T.subst x t)
  | .unOp op p => .unOp op (p.subst x t)
  | .binOp op p₁ p₂ => .binOp op (p₁.subst x t) (p₂.subst x t)

def Expr.Closed (X : Set PVar) : Expr → Prop
  | .pure p => p.Closed X
  | .error => True
  | .assume t => t.Closed X
  | .letIn bx e₁ e₂ =>
      e₁.Closed X ∧ e₂.Closed (match bx with | .anon => X | .named x => X ∪ {x})
  | .choice e₁ e₂ => e₁.Closed X ∧ e₂.Closed X
  | .alloc t => t.Closed X
  | .free t => t.Closed X
  | .store t₁ t₂ => t₁.Closed X ∧ t₂.Closed X
  | .load t => t.Closed X
  | .call _ _ ts => ∀ t ∈ ts, t.Closed X

def Expr.ClosedProgram (e : Expr) : Prop := e.Closed ∅

def Expr.substTerm (e : Expr) (x : PVar) (t : Term) : Expr :=
  match e with
  | .pure p => .pure (p.subst x t)
  | .error => .error
  | .assume T => .assume (T.subst x t)
  | .letIn bx e₁ e₂ =>
      .letIn bx (e₁.substTerm x t) (if bx = .named x then e₂ else e₂.substTerm x t)
  | .choice e₁ e₂ => .choice (e₁.substTerm x t) (e₂.substTerm x t)
  | .alloc T => .alloc (T.subst x t)
  | .free T => .free (T.subst x t)
  | .store T₁ T₂ => .store (T₁.subst x t) (T₂.subst x t)
  | .load T => .load (T.subst x t)
  | .call f τs Ts => .call f τs (Ts.map (·.subst x t))

/-- Substitute a value for a binder (`e ⌊ v // bx ⌋`). -/
def Expr.subst (e : Expr) (bx : Binder) (v : Val) : Expr :=
  match bx with
  | .anon => e
  | .named x => e.substTerm x (.val v)

/-- Substitution by a list of terms (`e ⌊ ts [//] xs ⌋ₜ`). -/
def Expr.substs (e : Expr) (xs : List PVar) (ts : List Term) : Expr :=
  (xs.zip ts).foldl (fun e (x, t) => e.substTerm x t) e

/-! ## Properties -/

namespace Term

@[simp] theorem ofVals_nil : ofVals [] = [] := rfl
@[simp] theorem ofVals_cons (v : Val) (vs : List Val) :
    ofVals (v :: vs) = .val v :: ofVals vs := rfl
@[simp] theorem ofVals_append (vs ws : List Val) :
    ofVals (vs ++ ws) = ofVals vs ++ ofVals ws := List.map_append ..
@[simp] theorem ofVals_length (vs : List Val) : (ofVals vs).length = vs.length :=
  List.length_map ..
@[simp] theorem ofVars_nil : ofVars [] = [] := rfl
@[simp] theorem ofVars_cons (x : PVar) (xs : List PVar) :
    ofVars (x :: xs) = .var x :: ofVars xs := rfl
@[simp] theorem ofVars_length (xs : List PVar) : (ofVars xs).length = xs.length :=
  List.length_map ..

end Term

@[simp] theorem Term.eval_var (x : PVar) : (Term.var x).eval = none := rfl
@[simp] theorem Term.eval_val (v : Val) : (Term.val v).eval = some v := rfl
@[simp] theorem Pure.eval_term (t : Term) : (Pure.term t).eval = t.eval := rfl

theorem Pure.eval_minus {p : Pure} {z : ℤ} (h : p.eval = some (.int z)) :
    (Pure.minus p).eval = some (.int (-z)) := by
  simp [eval, h, UnOp.eval]

theorem Pure.eval_not {p : Pure} {b : Bool} (h : p.eval = some (.bool b)) :
    (Pure.not p).eval = some (.bool !b) := by
  simp [eval, h, UnOp.eval]

theorem Pure.eval_add {p₁ p₂ : Pure} {z₁ z₂ : ℤ}
    (h₁ : p₁.eval = some (.int z₁)) (h₂ : p₂.eval = some (.int z₂)) :
    (Pure.add p₁ p₂).eval = some (.int (z₁ + z₂)) := by
  simp [eval, h₁, h₂, BinOp.eval]

theorem Pure.eval_mod {p₁ p₂ : Pure} {z₁ z₂ : ℤ}
      (h₁ : p₁.eval = some (.int z₁)) (h₂ : p₂.eval = some (.int z₂)) :
      (Pure.mod p₁ p₂).eval = some (.int (z₁.tmod z₂)) := by
    simp [eval, h₁, h₂, BinOp.eval]

theorem Pure.eval_eq {p₁ p₂ : Pure} {v₁ v₂ : Val}
    (h₁ : p₁.eval = some v₁) (h₂ : p₂.eval = some v₂) :
    (Pure.eq p₁ p₂).eval = some (.bool (decide (v₁ = v₂))) := by
  simp [eval, h₁, h₂, BinOp.eval]

theorem Pure.eval_lt {p₁ p₂ : Pure} {z₁ z₂ : ℤ}
    (h₁ : p₁.eval = some (.int z₁)) (h₂ : p₂.eval = some (.int z₂)) :
    (Pure.lt p₁ p₂).eval = some (.bool (decide (z₁ < z₂))) := by
  simp [eval, h₁, h₂, BinOp.eval]

theorem Pure.eval_offset {p₁ p₂ : Pure} {l : Loc} {z : ℤ}
    (h₁ : p₁.eval = some (.loc l)) (h₂ : p₂.eval = some (.int z)) :
    (Pure.offset p₁ p₂).eval = some (.loc (l +ₗ z.toNat)) := by
  simp [eval, h₁, h₂, BinOp.eval]

@[simp] theorem Expr.substs_nil_left (e : Expr) (ts : List Term) : e.substs [] ts = e := rfl
@[simp] theorem Expr.substs_nil_right (e : Expr) (xs : List PVar) : e.substs xs [] = e := by
  simp [substs]
@[simp] theorem Expr.substs_cons (e : Expr) (x : PVar) (xs : List PVar)
    (t : Term) (ts : List Term) :
    e.substs (x :: xs) (t :: ts) = (e.substTerm x t).substs xs ts := rfl

theorem Expr.substs_append (e : Expr) {xs ys : List PVar} {ts us : List Term}
    (hlen : xs.length = ts.length) :
    e.substs (xs ++ ys) (ts ++ us) = (e.substs xs ts).substs ys us := by
  simp only [Expr.substs, List.zip_append hlen, List.foldl_append]

theorem Term.subst_ofVals (x : PVar) (t : Term) (vs : List Val) :
    (Term.ofVals vs).map (·.subst x t) = Term.ofVals vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp_all [Term.subst]

theorem Term.subst_ofVars (x : PVar) (t : Term) {xs : List PVar} (hx : x ∉ xs) :
    (Term.ofVars xs).map (·.subst x t) = Term.ofVars xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rw [List.mem_cons, not_or] at hx
    rw [ofVars_cons, List.map_cons, ih hx.2]
    congr 1
    have hne : (Term.var y) ≠ (Term.var x) := by
      simp only [ne_eq, Term.var.injEq]
      exact fun h => hx.1 h.symm
    rw [Term.subst, if_neg hne]

/-! ### Monotonicity of closedness -/

theorem Term.Closed.mono {X Y : Set PVar} {t : Term}
    (h : t.Closed X) (hsub : X ⊆ Y) : t.Closed Y := by
  cases t with
  | var x => exact hsub h
  | val v => trivial

theorem Pure.Closed.mono {X Y : Set PVar} {p : Pure}
    (h : p.Closed X) (hsub : X ⊆ Y) : p.Closed Y := by
  induction p with
  | term t => exact Term.Closed.mono h hsub
  | unOp op p ih => exact ih h
  | binOp op p₁ p₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Expr.Closed.mono {X Y : Set PVar} {e : Expr}
    (h : e.Closed X) (hsub : X ⊆ Y) : e.Closed Y := by
  induction e generalizing X Y with
  | pure p => exact Pure.Closed.mono h hsub
  | error => trivial
  | assume t => exact Term.Closed.mono h hsub
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    refine ⟨ih₁ h.1 hsub, ?_⟩
    cases bx with
    | anon => exact ih₂ h.2 hsub
    | named x => exact ih₂ h.2 (Set.union_subset_union_left _ hsub)
  | choice e₁ e₂ ih₁ ih₂ => exact ⟨ih₁ h.1 hsub, ih₂ h.2 hsub⟩
  | alloc t => exact Term.Closed.mono h hsub
  | free t => exact Term.Closed.mono h hsub
  | store t₁ t₂ => exact ⟨Term.Closed.mono h.1 hsub, Term.Closed.mono h.2 hsub⟩
  | load t => exact Term.Closed.mono h hsub
  | call f τs ts => exact fun t hin => Term.Closed.mono (h t hin) hsub

/-! ### Commutativity of substitution -/

theorem Term.subst_comm {t : Term} {x y : PVar} {vx vy : Val} (hxy : y ≠ x) :
    (t.subst y (Term.val vy)).subst x (Term.val vx)
      = (t.subst x (Term.val vx)).subst y (Term.val vy) := by
  cases t with
  | var x =>
    simp [Term.subst]
    split_ifs <;> simp_all
  | val v => rfl

theorem Pure.subst_comm {p : Pure} {x y : PVar} {vx vy : Val} (hxy : y ≠ x) :
    (p.subst y (Term.val vy)).subst x (Term.val vx)
      = (p.subst x (Term.val vx)).subst y (Term.val vy) := by
  induction p <;> simp [Pure.subst]
  case term t => exact t.subst_comm hxy
  case unOp op p ih => exact ih
  case binOp op p₁ p₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

theorem Expr.substTerm_comm {e : Expr} {x y : PVar} {vx vy : Val} (hxy : y ≠ x) :
    (e.substTerm y (Term.val vy)).substTerm x (Term.val vx)
      = (e.substTerm x (Term.val vx)).substTerm y (Term.val vy) := by
  induction e <;> simp [Expr.substTerm, Term.subst]
  case pure p => exact p.subst_comm hxy
  case assume T => exact T.subst_comm hxy
  case letIn bx e₁ e₂ ih₁ ih₂ =>
    refine ⟨ih₁, ?_⟩
    cases bx with
    | anon => simp [ih₂]
    | named z => split_ifs <;> simp_all
  case choice e₁ e₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  case alloc T => exact T.subst_comm hxy
  case free T => exact T.subst_comm hxy
  case store T₁ T₂ => exact ⟨T₁.subst_comm hxy, T₂.subst_comm hxy⟩
  case load T => exact T.subst_comm hxy
  case call f τs ts => exact fun T _ => T.subst_comm hxy

theorem Expr.substTerm_substs_comm {e : Expr} {x : PVar} {v : Val}
    {xs : List PVar} {vs : List Val} (hx : x ∉ xs) :
    (e.substs xs (Term.ofVals vs)).substTerm x (.val v)
      = (e.substTerm x (.val v)).substs xs (Term.ofVals vs) := by
  induction xs generalizing e vs with
  | nil => rfl
  | cons y ys ih =>
    cases vs with
    | nil => rfl
    | cons v' vs' =>
      simp [substs_cons]
      rw [ih (by simp_all), e.substTerm_comm (by intro rfl; exact hx (by simp))]

theorem Expr.substs_comm {e : Expr} {ys : List PVar} {ws : List Val} :
    ∀ {xs : List PVar} {vs : List Val}, (∀ x ∈ xs, x ∉ ys) →
      (e.substs xs (Term.ofVals vs)).substs ys (Term.ofVals ws)
        = (e.substs ys (Term.ofVals ws)).substs xs (Term.ofVals vs) := by
  intro xs
  induction xs generalizing e with
  | nil => intro vs _; rfl
  | cons x xs ih =>
    intro vs hx
    cases vs with
    | nil => simp
    | cons v vs =>
      rw [Term.ofVals_cons, Expr.substs_cons, Expr.substs_cons,
        Expr.substTerm_substs_comm (hx x (by simp)),
        ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))]

/-! ### Idempotence of substitution under closedness -/

theorem Term.Closed.subst_eq {X : Set PVar} {T : Term} {x : PVar} (t : Term)
    (h : T.Closed X) (hx : x ∉ X) : T.subst x t = T := by
  cases T <;> simp_all [Term.Closed, Term.subst]
  intro heq; subst heq; exact absurd h hx

theorem Pure.Closed.subst_eq {X : Set PVar} {p : Pure} {x : PVar} (t : Term)
    (h : p.Closed X) (hx : x ∉ X) : p.subst x t = p := by
  induction p with
  | term T => exact congrArg _ (Term.Closed.subst_eq t h hx)
  | unOp op p ih => simp_all [Pure.Closed, Pure.subst]
  | binOp op p₁ p₂ ih₁ ih₂ => simp_all [Pure.Closed, Pure.subst]

theorem Expr.Closed.subst_eq {X : Set PVar} {e : Expr} {x : PVar} (t : Term)
    (h : e.Closed X) (hx : x ∉ X) : e.substTerm x t = e := by
  induction e generalizing X with
  | pure p => exact congrArg _ (Pure.Closed.subst_eq t h hx)
  | error => rfl
  | assume T => exact congrArg _ (Term.Closed.subst_eq t h hx)
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    have he₂ : (if bx = .named x then e₂ else e₂.substTerm x t) = e₂ := by
      by_cases hbx : bx = .named x
      · simp [hbx]
      · rw [if_neg hbx]
        cases bx with
        | anon => exact ih₂ h₂ hx
        | named y =>
          refine ih₂ h₂ ?_
          intro hmem
          rcases Set.mem_union .. |>.mp hmem with hX | hy
          · exact hx hX
          · rw [Set.mem_singleton_iff] at hy
            exact hbx (by rw [hy])
    simp [Expr.substTerm, ih₁ h₁ hx, he₂]
  | choice e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    simp [Expr.substTerm, ih₁ h₁ hx, ih₂ h₂ hx]
  | alloc T => exact congrArg _ (Term.Closed.subst_eq t h hx)
  | free T => exact congrArg _ (Term.Closed.subst_eq t h hx)
  | store T₁ T₂ =>
    obtain ⟨h₁, h₂⟩ := h
    simp [Expr.substTerm, Term.Closed.subst_eq t h₁ hx, Term.Closed.subst_eq t h₂ hx]
  | load T => exact congrArg _ (Term.Closed.subst_eq t h hx)
  | call f τs Ts =>
    have : Ts.map (·.subst x t) = Ts.map id :=
      List.map_congr_left fun T hT => Term.Closed.subst_eq t (h T hT) hx
    simp [Expr.substTerm, this]

theorem Expr.Closed.substs_eq {X : Set PVar} {e : Expr} (h : e.Closed X) :
    ∀ {xs : List PVar} {ts : List Term}, (∀ x ∈ xs, x ∉ X) → e.substs xs ts = e := by
  intro xs
  induction xs with
  | nil => intro _ _; rfl
  | cons x xs ih =>
    intro ts hx
    cases ts with
    | nil => simp
    | cons t ts =>
      rw [Expr.substs_cons, Expr.Closed.subst_eq t h (hx x (by simp))]
      exact ih fun y hy => hx y (List.mem_cons_of_mem _ hy)

/-! ### Preservation of closedness under substitution -/

theorem Term.Closed.subst_val {X : Set PVar} {t : Term} (x : PVar) (v : Val)
    (h : t.Closed X) : (t.subst x (.val v)).Closed X := by
  cases t with
  | var y =>
    by_cases hy : (Term.var y) = .var x
    · simp [Term.subst, hy, Term.Closed]
    · simpa [Term.subst, hy, Term.Closed] using h
  | val w => trivial

theorem Pure.Closed.subst_val {X : Set PVar} {p : Pure} (x : PVar) (v : Val)
    (h : p.Closed X) : (p.subst x (.val v)).Closed X := by
  induction p with
  | term t => exact Term.Closed.subst_val x v h
  | unOp op p ih => exact ih h
  | binOp op p₁ p₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Expr.Closed.subst_val {X : Set PVar} {e : Expr} (x : PVar) (v : Val)
    (h : e.Closed X) : (e.substTerm x (.val v)).Closed X := by
  induction e generalizing X with
  | pure p => exact Pure.Closed.subst_val x v h
  | error => trivial
  | assume t => exact Term.Closed.subst_val x v h
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    refine ⟨ih₁ h.1, ?_⟩
    by_cases hbx : bx = .named x
    · simpa [Expr.substTerm, hbx] using h.2
    · simpa [Expr.substTerm, hbx] using ih₂ h.2
  | choice e₁ e₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | alloc t => exact Term.Closed.subst_val x v h
  | free t => exact Term.Closed.subst_val x v h
  | store t₁ t₂ => exact ⟨Term.Closed.subst_val x v h.1, Term.Closed.subst_val x v h.2⟩
  | load t => exact Term.Closed.subst_val x v h
  | call f τs ts =>
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact Term.Closed.subst_val x v (h t' ht')

theorem Term.Closed.subst_erase {X : Set PVar} {x : PVar} {v : Val} {t : Term}
    (h : t.Closed (X ∪ {x})) : (t.subst x (.val v)).Closed X := by
  cases t with
  | var y =>
    by_cases hy : y = x
    · subst hy
      rw [Term.subst, if_pos rfl]
      trivial
    · rw [Term.subst, if_neg (by simpa using hy)]
      rcases h with h | h
      · exact h
      · exact absurd h hy
  | val w => trivial

theorem Pure.Closed.subst_erase {X : Set PVar} {x : PVar} {v : Val} {p : Pure}
    (h : p.Closed (X ∪ {x})) : (p.subst x (.val v)).Closed X := by
  induction p with
  | term t => exact Term.Closed.subst_erase h
  | unOp op p ih => exact ih h
  | binOp op p₁ p₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Expr.Closed.subst_erase {x : PVar} {v : Val} :
    ∀ {e : Expr} {X : Set PVar}, e.Closed (X ∪ {x}) → (e.substTerm x (.val v)).Closed X := by
  intro e
  induction e with
  | pure p => intro X h; exact Pure.Closed.subst_erase h
  | error => intro X _; trivial
  | assume t => intro X h; exact Term.Closed.subst_erase h
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    intro X h
    refine ⟨ih₁ h.1, ?_⟩
    cases bx with
    | anon => exact ih₂ h.2
    | named y =>
      by_cases hy : y = x
      · subst hy
        show Expr.Closed (X ∪ {y}) (if (Binder.named y) = .named y then e₂ else _)
        rw [if_pos rfl]
        refine Expr.Closed.mono h.2 ?_
        rintro z ((hz | hz) | hz)
        · exact Or.inl hz
        · exact Or.inr hz
        · exact Or.inr hz
      · show Expr.Closed (X ∪ {y})
          (if (Binder.named y) = .named x then e₂ else e₂.substTerm x (.val v))
        rw [if_neg (by simpa using hy)]
        refine ih₂ (X := X ∪ {y}) (Expr.Closed.mono h.2 ?_)
        rintro z ((hz | hz) | hz)
        · exact Or.inl (Or.inl hz)
        · exact Or.inr hz
        · exact Or.inl (Or.inr hz)
  | choice e₁ e₂ ih₁ ih₂ => intro X h; exact ⟨ih₁ h.1, ih₂ h.2⟩
  | alloc t => intro X h; exact Term.Closed.subst_erase h
  | free t => intro X h; exact Term.Closed.subst_erase h
  | store t₁ t₂ =>
    intro X h; exact ⟨Term.Closed.subst_erase h.1, Term.Closed.subst_erase h.2⟩
  | load t => intro X h; exact Term.Closed.subst_erase h
  | call f τs ts =>
    intro X h t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact Term.Closed.subst_erase (h t' ht')

theorem Expr.Closed.substs_erase :
    ∀ {xs : List PVar} {vs : List Val} {e : Expr} {X : Set PVar},
      e.Closed (X ∪ {y | y ∈ xs}) → xs.length = vs.length →
      (e.substs xs (Term.ofVals vs)).Closed X := by
  intro xs
  induction xs with
  | nil =>
    intro vs e X h _
    refine Expr.Closed.mono h ?_
    rintro z (hz | hz)
    · exact hz
    · simp at hz
  | cons x xs ih =>
    intro vs e X h hlen
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      rw [Term.ofVals_cons, Expr.substs_cons]
      refine ih (X := X) ?_ (by simpa using hlen)
      refine Expr.Closed.subst_erase (X := X ∪ {y | y ∈ xs}) (Expr.Closed.mono h ?_)
      rintro z (hz | hz)
      · exact Or.inl (Or.inl hz)
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inr rfl
        · exact Or.inl (Or.inr hz)

/-! ### Substitution in program expressions -/

theorem Expr.substs_call {f : Fid} {τs : List Ty} {xs : List PVar} {vs : List Val}
    (hlen : xs.length = vs.length) (hdup : xs.Nodup) :
    (Expr.call f τs (Term.ofVars xs)).substs xs (Term.ofVals vs)
      = .call f τs (Term.ofVals vs) := by
  suffices h : ∀ (xs : List PVar) (acc vs : List Val), xs.length = vs.length → xs.Nodup →
      (Expr.call f τs (Term.ofVals acc ++ Term.ofVars xs)).substs xs (Term.ofVals vs)
        = .call f τs (Term.ofVals (acc ++ vs)) by
    simpa using h xs [] vs hlen hdup
  intro xs
  induction xs with
  | nil =>
    intro acc vs hlen _
    obtain rfl : vs = [] := by simpa using hlen.symm
    simp [Term.ofVars]
  | cons x xs ih =>
    intro acc vs hlen hdup
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [Term.ofVals_cons, Expr.substs_cons]
      have hx : x ∉ xs := (List.nodup_cons.mp hdup).1
      have hsub : (Expr.call f τs (Term.ofVals acc ++ Term.ofVars (x :: xs))).substTerm x (.val v)
          = .call f τs (Term.ofVals (acc ++ [v]) ++ Term.ofVars xs) := by
        simp only [Expr.substTerm, Term.ofVars_cons, List.map_append, List.map_cons,
          Term.subst_ofVals, Term.subst_ofVars x _ hx, Term.ofVals_append]
        simp [Term.subst]
      rw [hsub, ih (acc ++ [v]) vs (by simpa using hlen) (List.nodup_cons.mp hdup).2]
      simp

theorem Expr.substs_letIn {x : PVar} {xs : List PVar} {vs : List Val} {e₁ e₂ : Expr}
    (hlen : xs.length = vs.length) (hx : x ∉ xs) (hclosed : e₁.ClosedProgram) :
    (Expr.letIn (.named x) e₁ e₂).substs xs (Term.ofVals vs)
      = Expr.letIn (.named x) e₁ (e₂.substs xs (Term.ofVals vs)) := by
  induction xs generalizing vs e₂ with
  | nil =>
    obtain rfl : vs = [] := by simpa using hlen.symm
    rfl
  | cons y ys ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hxy : x ≠ y := by rintro rfl; simp at hx
      have hsub : (Expr.letIn (.named x) e₁ e₂).substTerm y (.val v)
          = Expr.letIn (.named x) e₁ (e₂.substTerm y (.val v)) := by
        simp only [Expr.substTerm]
        rw [if_neg (by simpa using hxy), Expr.Closed.subst_eq _ hclosed (by simp)]
      simp only [Term.ofVals_cons, Expr.substs_cons, hsub]
      exact ih (by simpa using hlen) (by simp_all)

theorem Expr.substs_letIn_named {x : PVar} {e₁ e₂ : Expr} :
    ∀ {xs : List PVar} {vs : List Val}, x ∉ xs →
      (Expr.letIn (.named x) e₁ e₂).substs xs (Term.ofVals vs)
        = Expr.letIn (.named x) (e₁.substs xs (Term.ofVals vs))
          (e₂.substs xs (Term.ofVals vs)) := by
  intro xs
  induction xs generalizing e₁ e₂ with
  | nil => intro _ _; rfl
  | cons y ys ih =>
    intro vs hx
    cases vs with
    | nil => simp
    | cons v vs =>
      have hxy : (Binder.named x) ≠ .named y := by simpa using fun h => hx (by simp [h])
      rw [Term.ofVals_cons, Expr.substs_cons, Expr.substs_cons, Expr.substs_cons]
      show ((Expr.letIn (.named x) (e₁.substTerm y (.val v))
        (if (Binder.named x) = .named y then e₂ else e₂.substTerm y (.val v))).substs ys
          (Term.ofVals vs)) = _
      rw [if_neg hxy, ih (fun h => hx (List.mem_cons_of_mem _ h))]

end RUXt
