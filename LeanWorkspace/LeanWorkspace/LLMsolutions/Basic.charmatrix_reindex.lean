FAIL
import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_reindex (e : n ≃ m) :
    Matrix.charmatrix (Matrix.reindex e e M) = Matrix.reindex e e (Matrix.charmatrix M) := by
  ext i j
  simp only [Matrix.charmatrix, Matrix.sub_apply, Matrix.reindex_apply]
  congr 1
  ext k l
  by_cases h : k = l
  · subst h
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, h]
