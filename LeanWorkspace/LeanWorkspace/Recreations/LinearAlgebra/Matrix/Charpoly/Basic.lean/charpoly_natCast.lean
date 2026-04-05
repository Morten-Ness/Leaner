import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_natCast (k : ℕ) :
    Matrix.charpoly (k : Matrix n n R) = (Polynomial.X - (k : R[Polynomial.X])) ^ Fintype.card n := by
  simp [Matrix.charpoly]

