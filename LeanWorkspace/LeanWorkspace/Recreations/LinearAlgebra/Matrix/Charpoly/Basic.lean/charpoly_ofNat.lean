import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_ofNat (k : ℕ) [k.AtLeastTwo] :
    Matrix.charpoly (ofNat(k) : Matrix n n R) = (Polynomial.X - ofNat(k)) ^ Fintype.card n := Matrix.charpoly_natCast _

