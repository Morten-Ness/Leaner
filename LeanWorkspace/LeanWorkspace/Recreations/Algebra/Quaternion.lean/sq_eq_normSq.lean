import Mathlib

variable {R : Type*}

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}

theorem sq_eq_normSq : a ^ 2 = Quaternion.normSq a ↔ a = a.re := by
  rw [← Quaternion.star_eq_self, ← Quaternion.star_mul_self, sq, mul_eq_mul_right_iff, eq_comm]
  exact or_iff_left_of_imp fun ha ↦ ha.symm ▸ star_zero _

