import Mathlib

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [Finite m] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

theorem Matrix.toLin_scalar (r : R) : Matrix.toLin v₁ v₁ (Matrix.scalar n r) = r • LinearMap.id := (LinearMap.toMatrix v₁ v₁).injective (by simp [toMatrix_id, smul_one_eq_diagonal])

