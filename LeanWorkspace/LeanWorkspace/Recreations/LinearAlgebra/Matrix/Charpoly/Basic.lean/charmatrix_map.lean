import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_map (M : Matrix n n R) (f : R →+* S) :
    Matrix.charmatrix (M.map f) = (Matrix.charmatrix M).map (Polynomial.map f) := by
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.charmatrix, diagonal]

