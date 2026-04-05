import Mathlib

variable {R : Type*}

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}

theorem sq_eq_neg_normSq : a ^ 2 = -Quaternion.normSq a ↔ a.re = 0 := by
  simp_rw [← Quaternion.star_eq_neg]
  obtain rfl | hq0 := eq_or_ne a 0
  · simp
  · rw [← Quaternion.star_mul_self, ← mul_neg, ← neg_sq, sq, mul_left_inj' (neg_ne_zero.mpr hq0), eq_comm]

