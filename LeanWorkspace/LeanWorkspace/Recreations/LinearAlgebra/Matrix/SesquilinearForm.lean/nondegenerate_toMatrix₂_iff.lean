import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
  {M : Matrix m n R}

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
  (b₁ : Basis m R M₁) (b₂ : Basis n R M₂) {B : M₁ →ₗ[R] M₂ →ₗ[R] R}

theorem nondegenerate_toMatrix₂_iff :
    (toMatrix₂ b₁ b₂ B).Nondegenerate ↔ B.Nondegenerate := (Matrix.nondegenerate_toLinearMap₂_iff b₁ b₂).symm.trans <|
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

