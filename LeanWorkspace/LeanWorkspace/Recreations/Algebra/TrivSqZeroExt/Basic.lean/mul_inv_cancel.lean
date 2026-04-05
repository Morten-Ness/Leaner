import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

variable [SMulCommClass R Rᵐᵒᵖ M]

theorem mul_inv_cancel {x : tsze R M} (hx : TrivSqZeroExt.fst x ≠ 0) : x * x⁻¹ = 1 := by
  have : Invertible x.fst := Units.invertible (.mk0 _ hx)
  have := invertibleOfInvertibleFst x
  rw [← invOf_eq_inv, mul_invOf_self]

