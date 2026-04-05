import Mathlib

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [Finite m] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)

theorem LinearMap.toMatrix_map_left (f : M₃ →ₗ[R] M₂) (g : M₁ ≃ₗ[R] M₃) :
    f.toMatrix (v₁.map g) v₂ = (f ∘ₗ g.toLinearMap).toMatrix v₁ v₂ := by
  rfl

