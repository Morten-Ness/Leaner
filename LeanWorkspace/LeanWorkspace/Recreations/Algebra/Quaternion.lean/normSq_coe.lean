import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem normSq_coe : Quaternion.normSq (x : ℍ[R]) = x ^ 2 := by
  rw [Quaternion.normSq_def, Quaternion.star_coe, ← Quaternion.coe_mul, Quaternion.re_coe, sq]

