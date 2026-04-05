import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inr_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M) :
    (TrivSqZeroExt.inr m₁ * TrivSqZeroExt.inr m₂ : tsze R M) = 0 := TrivSqZeroExt.ext (mul_zero _) <|
    show (0 : R) •> m₂ + m₁ <• (0 : R) = 0 by rw [zero_smul, zero_add, op_zero, zero_smul]

