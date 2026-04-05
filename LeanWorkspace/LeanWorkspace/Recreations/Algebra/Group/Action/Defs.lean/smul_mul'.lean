import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [Monoid N] [MulDistribMulAction M N]

theorem smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • b₂ := MulDistribMulAction.smul_mul ..

