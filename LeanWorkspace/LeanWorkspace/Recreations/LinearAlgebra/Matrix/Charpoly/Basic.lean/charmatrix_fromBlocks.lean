import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_fromBlocks :
    Matrix.charmatrix (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (Matrix.charmatrix M₁₁) (- M₁₂.map Polynomial.C) (- M₂₁.map Polynomial.C) (Matrix.charmatrix M₂₂) := by
  simp only [Matrix.charmatrix]
  ext (i | i) (j | j) : 2 <;> simp [diagonal]

-- TODO: importing block triangular here is somewhat expensive, if more lemmas about it are added
-- to this file, it may be worth extracting things out to Charpoly/Block.lean

