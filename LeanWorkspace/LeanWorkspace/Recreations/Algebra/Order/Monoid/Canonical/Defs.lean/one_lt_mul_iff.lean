import Mathlib

variable {α : Type u}

variable [CommMonoid α]

variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

theorem one_lt_mul_iff : 1 < a * b ↔ 1 < a ∨ 1 < b := by
  simp only [one_lt_iff_ne_one, Ne, mul_eq_one, not_and_or]

