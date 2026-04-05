import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem normSq_star : Quaternion.normSq (star a) = Quaternion.normSq a := by simp [Quaternion.normSq_def']

