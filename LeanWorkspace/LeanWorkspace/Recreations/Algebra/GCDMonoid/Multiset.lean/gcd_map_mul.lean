import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_map_mul (a : α) (s : Multiset α) : (s.map (a * ·)).gcd = normalize a * s.gcd := by
  refine s.induction_on ?_ fun b s ih ↦ ?_
  · simp_rw [map_zero, Multiset.gcd_zero, mul_zero]
  · simp_rw [map_cons, Multiset.gcd_cons, ← gcd_mul_left]
    rw [ih]
    apply ((normalize_associated a).mul_right _).gcd_eq_right

