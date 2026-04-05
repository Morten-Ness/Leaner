import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_zero : Matrix.charmatrix (0 : Matrix n n R) = Matrix.scalar n (Polynomial.X : R[Polynomial.X]) := by
  simp [Matrix.charmatrix]

