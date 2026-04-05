import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem pow_eq_aeval_mod_charpoly (M : Matrix n n R) (k : ℕ) :
    M ^ k = Polynomial.aeval M (Polynomial.X ^ k %ₘ M.charpoly) := by rw [← Matrix.aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

