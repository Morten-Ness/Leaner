import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  simpa using Matrix.charpoly_monic M
