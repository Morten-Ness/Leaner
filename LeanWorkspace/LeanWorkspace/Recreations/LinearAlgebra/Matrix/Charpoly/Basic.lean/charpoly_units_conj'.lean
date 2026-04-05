import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_units_conj' (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M⁻¹.val * N * M.val).charpoly = N.charpoly := Matrix.charpoly_units_conj M⁻¹ N

set_option backward.isDefEq.respectTransparency false in

