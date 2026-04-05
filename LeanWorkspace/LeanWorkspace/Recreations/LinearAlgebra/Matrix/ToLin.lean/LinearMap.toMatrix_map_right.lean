import Mathlib

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [Finite m] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)

theorem LinearMap.toMatrix_map_right (f : M₁ →ₗ[R] M₃) (g : M₂ ≃ₗ[R] M₃) :
    f.toMatrix v₁ (v₂.map g) = (g.symm.toLinearMap ∘ₗ f).toMatrix v₁ v₂ := by
  rfl

