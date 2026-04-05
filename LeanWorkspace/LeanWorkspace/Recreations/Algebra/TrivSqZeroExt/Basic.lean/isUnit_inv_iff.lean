import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

variable [SMulCommClass R Rᵐᵒᵖ M]

theorem isUnit_inv_iff {x : tsze R M} : IsUnit x⁻¹ ↔ IsUnit x := by
  simp_rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_inv, isUnit_iff_ne_zero, ne_eq, inv_eq_zero]

