import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inl_mul_eq_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r : R) (x : tsze R M) :
    TrivSqZeroExt.inl r * x = r •> x := TrivSqZeroExt.ext rfl (by dsimp; rw [smul_zero, add_zero])

