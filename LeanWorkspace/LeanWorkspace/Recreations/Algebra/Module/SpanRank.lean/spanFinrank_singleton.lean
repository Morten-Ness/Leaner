import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanFinrank_singleton {m : M} (hm : m ≠ 0) : (span R {m}).spanFinrank = 1 := by
  apply le_antisymm ?_ ?_
  · exact le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (by simp)) (by simp)
  · by_contra!
    simp [Submodule.spanFinrank_eq_zero_iff_eq_bot (fg_span_singleton m), hm] at this

