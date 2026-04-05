import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem self_mul_star : a * star a = Quaternion.normSq a := by rw [Quaternion.mul_star_eq_coe, Quaternion.normSq_def]

