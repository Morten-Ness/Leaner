import Mathlib

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

theorem LinearMap.toMatrix_toSpanSingleton [Finite m] (v₁ : Module.Basis n R R) (v₂ : Module.Basis m R M₂)
    (x : M₂) : (toSpanSingleton R M₂ x).toMatrix v₁ v₂ = vecMulVec (v₂.repr x) v₁ := by
  ext; simp [toMatrix_apply, vecMulVec_apply, mul_comm]

