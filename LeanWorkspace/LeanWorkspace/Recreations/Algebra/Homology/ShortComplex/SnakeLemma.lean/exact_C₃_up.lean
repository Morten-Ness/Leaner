import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

theorem exact_C₃_up : (ShortComplex.mk S.v₀₁.τ₃ S.v₁₂.τ₃
    (by rw [← comp_τ₃, S.w₀₂, zero_τ₃])).Exact := exact_of_f_is_kernel _ S.h₀τ₃

