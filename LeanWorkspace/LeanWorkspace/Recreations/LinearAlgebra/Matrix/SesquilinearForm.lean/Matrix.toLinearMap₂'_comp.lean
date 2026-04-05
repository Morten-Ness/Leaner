import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable {R : Type*} [CommSemiring R]

variable [Fintype n] [Fintype m]

variable [DecidableEq n] [DecidableEq m]

variable [Fintype n'] [Fintype m']

variable [DecidableEq n'] [DecidableEq m']

theorem Matrix.toLinearMap₂'_comp (M : Matrix n m R) (P : Matrix n n' R) (Q : Matrix m m' R) :
    LinearMap.compl₁₂ (Matrix.toLinearMap₂' R M) (toLin' P) (toLin' Q) =
      toLinearMap₂' R (Pᵀ * M * Q) := (LinearMap.toMatrix₂' R).injective (by simp)

