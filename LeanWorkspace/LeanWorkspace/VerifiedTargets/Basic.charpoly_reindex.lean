import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_reindex (e : n ≃ m)
    (M : Matrix n n R) : (Matrix.reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [Matrix.charmatrix_reindex, Matrix.det_reindex_self]

