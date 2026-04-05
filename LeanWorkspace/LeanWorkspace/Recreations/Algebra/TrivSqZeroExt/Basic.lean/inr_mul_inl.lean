import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inr_mul_inl [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (TrivSqZeroExt.inr m * TrivSqZeroExt.inl r : tsze R M) = TrivSqZeroExt.inr (m <• r) := TrivSqZeroExt.ext (zero_mul r) <|
    show (0 : R) •> (0 : M) + m <• r = m <• r by rw [smul_zero, zero_add]

