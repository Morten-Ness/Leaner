import Mathlib

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

theorem LinearMap.toMatrix_smulRight [Finite m] (f : M₁ →ₗ[R] R) (x : M₂) :
    toMatrix v₁ v₂ (f.smulRight x) = vecMulVec (v₂.repr x) (f ∘ v₁) := by
  ext i j
  simpa [toMatrix_apply, vecMulVec_apply] using mul_comm _ _

