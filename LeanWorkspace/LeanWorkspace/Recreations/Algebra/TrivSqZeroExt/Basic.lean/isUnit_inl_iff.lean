import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]

variable [SMulCommClass R Rᵐᵒᵖ M]

theorem isUnit_inl_iff {r : R} : IsUnit (TrivSqZeroExt.inl r : tsze R M) ↔ IsUnit r := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_inl]

