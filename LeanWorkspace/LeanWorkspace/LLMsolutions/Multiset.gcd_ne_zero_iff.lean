import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_ne_zero_iff (s : Multiset α) : s.gcd ≠ 0 ↔ ∃ x ∈ s, x ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      by_cases ha : a = 0
      · simp [Multiset.gcd_cons, ha, ih]
      · simp [Multiset.gcd_cons, ha, ih]
