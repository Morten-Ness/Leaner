import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val * N * M⁻¹.val).charpoly = N.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← mul_assoc]
  simp

