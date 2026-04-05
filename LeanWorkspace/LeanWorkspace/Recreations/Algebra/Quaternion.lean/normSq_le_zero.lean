import Mathlib

variable {R : Type*}

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}

theorem normSq_le_zero : Quaternion.normSq a ≤ 0 ↔ a = 0 := Quaternion.normSq_nonneg.ge_iff_eq'.trans Quaternion.normSq_eq_zero

