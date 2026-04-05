import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inl_mul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (TrivSqZeroExt.inl (r₁ * r₂) : tsze R M) = TrivSqZeroExt.inl r₁ * TrivSqZeroExt.inl r₂ := TrivSqZeroExt.ext rfl <| show (0 : M) = r₁ •> (0 : M) + (0 : M) <• r₂ by rw [smul_zero, zero_add, smul_zero]

