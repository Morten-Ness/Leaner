import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

theorem one_mk_mul_one_mk [MulOneClass M] [Mul N] (b₁ b₂ : N) :
    ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂) := by
  rw [mk_mul_mk, mul_one]

