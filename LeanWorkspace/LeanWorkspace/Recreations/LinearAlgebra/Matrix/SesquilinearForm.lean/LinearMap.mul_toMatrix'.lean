import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable {R : Type*} [CommSemiring R]

variable [Fintype n] [Fintype m]

variable [DecidableEq n] [DecidableEq m]

variable [Fintype n'] [Fintype m']

variable [DecidableEq n'] [DecidableEq m']

theorem LinearMap.mul_toMatrix' (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : Matrix n' n R) :
    M * toMatrix₂' R B = toMatrix₂' R (B.comp <| toLin' Mᵀ) := by
  simp only [B.toMatrix₂'_comp, transpose_transpose, toMatrix'_toLin']

