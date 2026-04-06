import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_fromBlocks :
    Matrix.charmatrix (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (Matrix.charmatrix M₁₁) (- M₁₂.map Polynomial.C) (- M₂₁.map Polynomial.C) (Matrix.charmatrix M₂₂) := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.charmatrix, Matrix.fromBlocks, Matrix.diagonal, Matrix.map_apply]
