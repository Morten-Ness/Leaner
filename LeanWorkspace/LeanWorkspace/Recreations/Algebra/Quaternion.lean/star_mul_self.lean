import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem star_mul_self : star a * a = Quaternion.normSq a := by rw [star_comm_self, Quaternion.self_mul_star]

