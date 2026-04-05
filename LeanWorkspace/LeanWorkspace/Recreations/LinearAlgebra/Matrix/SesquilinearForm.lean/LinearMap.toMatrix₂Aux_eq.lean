import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommSemiring R]

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂]
  [Module R N₂]

variable {σ₁ : R →+* R} {σ₂ : R →+* R} [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)

theorem LinearMap.toMatrix₂Aux_eq (B : M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] N₂) :
    LinearMap.toMatrix₂Aux R b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B := Matrix.ext fun i j => by rw [LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂Aux_apply]

