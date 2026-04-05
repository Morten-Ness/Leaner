import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_apply_eq : Matrix.charmatrix M i i = (X : R[X]) - C (M i i) := by
  simp only [Matrix.charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, map_apply,
    diagonal_apply_eq]

