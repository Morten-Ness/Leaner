import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_diagonal (d : n → R) :
    Matrix.charmatrix (diagonal d) = diagonal fun i => Polynomial.X - Polynomial.C (d i) := by
  rw [Matrix.charmatrix, scalar_apply, RingHom.mapMatrix_apply, diagonal_map (map_zero _), diagonal_sub]

