import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem normSq_neg : Quaternion.normSq (-a) = Quaternion.normSq a := by simp only [Quaternion.normSq_def, star_neg, neg_mul_neg]

