import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_apply_ne (h : i ≠ j) : Matrix.charmatrix M i j = -Polynomial.C (M i j) := by
  simp [Matrix.charmatrix, h]
