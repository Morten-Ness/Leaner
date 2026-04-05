import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem im_sq : a.im ^ 2 = -Quaternion.normSq a.im := by
  simp_rw [sq, ← Quaternion.star_mul_self, Quaternion.star_im, neg_mul, neg_neg]

