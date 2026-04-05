import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_reindex (e : n ≃ m) :
    Matrix.charmatrix (reindex e e M) = reindex e e (Matrix.charmatrix M) := by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]

