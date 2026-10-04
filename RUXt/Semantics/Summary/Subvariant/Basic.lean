import RUXt.Model.Summary.Basic
import RUXt.Semantics.Logic.Poly

/-!
# Well-shaped summaries and ownership through typed subvariants

Summaries whose source has one parameter per input value (`Summary.WellShaped`), and the
resources a value owns as an inhabitant of a type constructor, read through typed subvariant
arguments (`TyConsId.ownsAt`).
-/

namespace RUXt

/-! ## Summaries with one parameter per input value -/

/-- The source of a summary has one parameter per input value of its postcondition. -/
def Summary.WellShaped (ς : Summary) : Prop :=
  ς.src.fn.params.length = ς.valArity

namespace Summary

/-- A summary built with `Summary.of` is well-shaped. -/
theorem wellShaped_of (src : Source) (F) : (Summary.of src F).WellShaped := rfl

end Summary

/-! ## Owning resources through a typed subvariant -/

/-- The resources a value owns as an inhabitant of the type constructor `C` at rank `k`, read
through the typed subvariant arguments `S`: for a bare type parameter, the `k`-th subvariant of
the typed subvariant supplied for it; for any other constructor, the opaque predicate of its
instantiation at the types of `S`, or `false` if it uses a type parameter beyond `S`. -/
def TyConsId.ownsAt (C : TyConsId) (Λ : Library) {n : ℕ} (S : SubvArgs.{0} n) (k : ℕ)
    (v : Val) : Asrt.{0} :=
  match C with
  | .param i => (S.get i).get Λ k v
  | C => match C.instantiate (TeleArg.toList S.tys) with
    | some τ => .opaque Λ τ v
    | none => .false

/-- The resources a type parameter describes are the ones the typed subvariant supplied for
it describes, at the rank of the value. -/
@[simp] theorem TyConsId.ownsAt_param (i : ℕ) (Λ : Library) {n : ℕ} (S : SubvArgs.{0} n)
    (k : ℕ) (v : Val) :
    (TyConsId.param i).ownsAt Λ S k v = (S.get i).get Λ k v := rfl

/-- The resources a custom type constructor describes, when it only uses the type parameters
of the tuple of typed subvariants: the opaque predicate of its concretisation at the types of
that tuple. -/
theorem TyConsId.ownsAt_custom (name : Tid) (args : List TyConsId) (Λ : Library) {n : ℕ}
    (S : SubvArgs.{0} n) (k : ℕ) (v : Val) (h : (TyConsId.custom name args).Bounded n) :
    (TyConsId.custom name args).ownsAt Λ S k v
      = .opaque Λ ((TyConsId.custom name args).concretise S.tys) v := by
  simp only [TyConsId.ownsAt, TyConsId.instantiate_toList h]

end RUXt
