import Mathlib

variable {α : Type*}

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]

theorem IsOrderedCancelMonoid.of_mul_lt_mul_left {α : Type*} [CommMonoid α] [LinearOrder α]
    (hmul : ∀ a b c : α, b < c → a * b < a * c) : IsOrderedCancelMonoid α where
  mul_le_mul_left a b h c := by
    obtain rfl | h := eq_or_lt_of_le h
    · simp
    · simpa [mul_comm] using (hmul _ _ _ h).le
  le_of_mul_le_mul_left a b c h := by
    contrapose! h
    exact hmul _ _ _ h

