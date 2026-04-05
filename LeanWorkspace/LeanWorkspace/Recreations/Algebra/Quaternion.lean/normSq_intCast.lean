import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem normSq_intCast (z : ℤ) : Quaternion.normSq (z : ℍ[R]) = (z : R) ^ 2 := by
  rw [← Quaternion.coe_intCast, Quaternion.normSq_coe]

