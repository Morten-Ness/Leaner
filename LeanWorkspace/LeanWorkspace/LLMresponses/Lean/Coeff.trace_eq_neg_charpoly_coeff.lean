import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
    Matrix.trace M = -M.charpoly.coeff (Fintype.card n - 1) := by
  simpa using Matrix.trace_eq_neg_charpoly_coeff M
