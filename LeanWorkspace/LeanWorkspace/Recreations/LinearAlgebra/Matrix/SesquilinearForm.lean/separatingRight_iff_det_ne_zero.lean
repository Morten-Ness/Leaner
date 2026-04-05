import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
  {M : Matrix m n R}

variable [IsDomain R] {M : Matrix n n R}

variable [AddCommMonoid M₁] [Module R M₁]
  (b : Basis m R M₁) {B : M₁ →ₗ[R] M₁ →ₗ[R] R}

theorem separatingRight_iff_det_ne_zero :
    B.SeparatingRight ↔ (toMatrix₂ b b B).det ≠ 0 := by
  rw [← Matrix.separatingRight_iff_det_ne_zero, LinearMap.separatingRight_toMatrix₂_iff]

