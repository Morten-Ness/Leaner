import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] :
    IsCentralScalar M (AddSubmonoid A) :=
by
  constructor
  intro a S
  ext x
  constructor <;> intro hx
  · simpa [smul_eq_mul, op_smul_eq_smul] using hx
  · simpa [smul_eq_mul, op_smul_eq_smul] using hx
