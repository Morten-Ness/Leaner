import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem normSq_def : Quaternion.normSq a = (a * star a).re := rfl

