import Mathlib

variable {G H M N P R S : Type*}

variable {M N : Type*} [Mul M] [Mul N]

theorem mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) := rfl

