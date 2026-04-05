import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable {R : Type*} [CommSemiring R]

variable [Fintype n] [Fintype m]

variable [DecidableEq n] [DecidableEq m]

variable [Fintype n'] [Fintype m']

variable [DecidableEq n'] [DecidableEq m']

theorem LinearMap.mul_toMatrix₂'_mul (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : Matrix n' n R)
    (N : Matrix m m' R) :
    M * toMatrix₂' R B * N = toMatrix₂' R (B.compl₁₂ (toLin' Mᵀ) (toLin' N)) := by
  simp

