import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_fin_two [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.charpoly = Polynomial.X ^ 2 - Polynomial.C M.trace * Polynomial.X + Polynomial.C M.det := by
  simpa using Matrix.charpoly_fin_two (R := R) M
