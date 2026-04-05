import Mathlib

variable {R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBySet_iff_is_torsion_by_span :
    IsTorsionBySet R M s ↔ IsTorsionBySet R M (Ideal.span s) := by
  simpa only [Module.isTorsionBySet_iff_subset_annihilator] using Ideal.span_le.symm

