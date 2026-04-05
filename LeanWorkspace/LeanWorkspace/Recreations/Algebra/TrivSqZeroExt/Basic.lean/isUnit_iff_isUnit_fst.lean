import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]

variable [SMulCommClass R Rᵐᵒᵖ M]

theorem isUnit_iff_isUnit_fst {x : tsze R M} : IsUnit x ↔ IsUnit x.fst := by
  simp only [← nonempty_invertible_iff_isUnit, (TrivSqZeroExt.invertibleEquivInvertibleFst x).nonempty_congr]

