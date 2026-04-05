import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommSemiring R]

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂]
  [Module R N₂]

variable {σ₁ : R →+* R} {σ₂ : R →+* R} [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)

theorem Matrix.toLinearMapₛₗ₂_toMatrix₂ (B : M₁ →ₛₗ[σ₁] M₂ →ₗ[R] N₂) :
    Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂ (LinearMap.toMatrix₂ b₁ b₂ B) = B := (Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂).apply_symm_apply B

