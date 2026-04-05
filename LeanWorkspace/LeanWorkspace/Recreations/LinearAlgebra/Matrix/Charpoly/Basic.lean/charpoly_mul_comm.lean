import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_mul_comm (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpoly := (isRegular_X_pow _).left.eq_iff.mp <| Matrix.charpoly_mul_comm' A B

