import Mathlib

open scoped Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_apply_eq : Matrix.charmatrix M i i = (Polynomial.X : R[X]) - Polynomial.C (M i i) := by
  simp only [Matrix.charmatrix, RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.map_apply,
    Matrix.diagonal_apply_eq]

