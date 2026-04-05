import Mathlib

variable {R : Type*}

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}

theorem normSq_nonneg : 0 ≤ Quaternion.normSq a := by
  rw [Quaternion.normSq_def']
  apply_rules [sq_nonneg, add_nonneg]

