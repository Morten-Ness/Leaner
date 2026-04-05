import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inl_mul_inr [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (TrivSqZeroExt.inl r * TrivSqZeroExt.inr m : tsze R M) = TrivSqZeroExt.inr (r • m) := TrivSqZeroExt.ext (mul_zero r) <|
    show r • m + (0 : Rᵐᵒᵖ) • (0 : M) = r • m by rw [smul_zero, add_zero]

