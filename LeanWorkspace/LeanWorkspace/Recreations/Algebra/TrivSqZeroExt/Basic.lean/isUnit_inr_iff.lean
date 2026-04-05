import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]

variable [SMulCommClass R Rᵐᵒᵖ M]

theorem isUnit_inr_iff {m : M} : IsUnit (TrivSqZeroExt.inr m : tsze R M) ↔ Subsingleton R := by
  simp_rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_inr, isUnit_zero_iff, subsingleton_iff_zero_eq_one]

