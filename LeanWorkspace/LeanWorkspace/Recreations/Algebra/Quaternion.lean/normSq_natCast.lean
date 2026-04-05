import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem normSq_natCast (n : ℕ) : Quaternion.normSq (n : ℍ[R]) = (n : R) ^ 2 := by
  rw [← Quaternion.coe_natCast, Quaternion.normSq_coe]

