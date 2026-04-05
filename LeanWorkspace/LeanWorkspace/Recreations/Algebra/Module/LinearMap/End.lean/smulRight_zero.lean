import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]

variable [Semiring S] [Module R S] [Module S M] [IsScalarTower R S M]

theorem smulRight_zero (f : M₁ →ₗ[R] S) : f.smulRight (0 : M) = 0 := by ext; simp

