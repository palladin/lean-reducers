import Init.Data.Int.Lemmas

namespace LeanReducers

/--
A tiny law-carrying monoid record. This deliberately avoids Mathlib so the
library remains light and self-contained.
-/
structure MonoidSpec (α : Type) where
  unit : α
  combine : α → α → α
  assoc : ∀ a b c, combine (combine a b) c = combine a (combine b c)
  left_unit : ∀ a, combine unit a = a
  right_unit : ∀ a, combine a unit = a

/--
Minimal additive law class used by `.sum`. We keep it separate from Lean's
runtime `Add` instances because not every `Add` instance is associative in the
mathematical sense; notably, `Float` is intentionally not an instance.
-/
class LawfulAddMonoid (α : Type) [Add α] [OfNat α 0] : Prop where
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  zero_add : ∀ a : α, 0 + a = a
  add_zero : ∀ a : α, a + 0 = a

instance : LawfulAddMonoid Nat where
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero

instance : LawfulAddMonoid Int where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero

namespace MonoidSpec

def additive (α : Type) [Add α] [OfNat α 0] [LawfulAddMonoid α] :
    MonoidSpec α where
  unit := 0
  combine := (· + ·)
  assoc := LawfulAddMonoid.add_assoc
  left_unit := LawfulAddMonoid.zero_add
  right_unit := LawfulAddMonoid.add_zero

end MonoidSpec

end LeanReducers
