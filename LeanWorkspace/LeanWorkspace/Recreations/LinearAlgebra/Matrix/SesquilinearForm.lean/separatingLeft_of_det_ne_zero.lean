import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
  {M : Matrix m n R}

variable [IsDomain R] {M : Matrix n n R}

variable [AddCommMonoid M₁] [Module R M₁]
  (b : Basis m R M₁) {B : M₁ →ₗ[R] M₁ →ₗ[R] R}

theorem separatingLeft_of_det_ne_zero (h : (toMatrix₂ b b B).det ≠ 0) : B.SeparatingLeft := (LinearMap.separatingLeft_iff_det_ne_zero b).mpr h

