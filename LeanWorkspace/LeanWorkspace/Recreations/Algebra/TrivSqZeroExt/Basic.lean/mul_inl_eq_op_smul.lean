import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem mul_inl_eq_op_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (r : R) :
    x * TrivSqZeroExt.inl r = x <• r := TrivSqZeroExt.ext rfl (by dsimp; rw [smul_zero, zero_add])

