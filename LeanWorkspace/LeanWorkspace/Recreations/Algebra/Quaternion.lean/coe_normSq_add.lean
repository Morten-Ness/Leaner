import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_normSq_add : Quaternion.normSq (a + b) = Quaternion.normSq a + a * star b + b * star a + Quaternion.normSq b := by
  simp only [star_add, ← Quaternion.self_mul_star, mul_add, add_mul, add_assoc, add_left_comm]

