import Mathlib

variable {M N G H α β γ δ : Type*}

theorem smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M) (y : N) :
    x • (1 : N) * y = x • y := by rw [smul_mul_assoc, one_mul]

