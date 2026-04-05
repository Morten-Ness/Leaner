import Mathlib

variable {R : Type*}

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}

theorem normSq_ne_zero : Quaternion.normSq a ≠ 0 ↔ a ≠ 0 := Quaternion.normSq_eq_zero.not

