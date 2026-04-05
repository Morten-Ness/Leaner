import Mathlib

variable {R : Type*}

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}

theorem normSq_eq_zero : Quaternion.normSq a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ Quaternion.normSq.map_zero⟩
  rw [Quaternion.normSq_def', add_eq_zero_iff_of_nonneg, add_eq_zero_iff_of_nonneg, add_eq_zero_iff_of_nonneg]
    at h
  · apply Quaternion.ext a 0 <;> apply eq_zero_of_pow_eq_zero
    exacts [h.1.1.1, h.1.1.2, h.1.2, h.2]
  all_goals apply_rules [sq_nonneg, add_nonneg]

