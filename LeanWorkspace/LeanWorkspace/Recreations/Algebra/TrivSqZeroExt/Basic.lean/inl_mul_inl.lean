import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inl_mul_inl [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (TrivSqZeroExt.inl r₁ * TrivSqZeroExt.inl r₂ : tsze R M) = TrivSqZeroExt.inl (r₁ * r₂) := (TrivSqZeroExt.inl_mul M r₁ r₂).symm

