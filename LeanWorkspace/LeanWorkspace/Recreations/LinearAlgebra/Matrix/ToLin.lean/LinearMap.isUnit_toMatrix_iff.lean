import Mathlib

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

variable [Fintype m]

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)

theorem LinearMap.isUnit_toMatrix_iff {f : M₁ →ₗ[R] M₁} : IsUnit (f.toMatrix v₁ v₁) ↔ IsUnit f := isUnit_map_iff (LinearMap.toMatrixAlgEquiv _) f

