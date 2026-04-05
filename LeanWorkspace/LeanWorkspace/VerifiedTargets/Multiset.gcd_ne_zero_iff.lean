import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_ne_zero_iff (s : Multiset α) : s.gcd ≠ 0 ↔ ∃ x ∈ s, x ≠ 0 := by
  simp [Multiset.gcd_eq_zero_iff]

