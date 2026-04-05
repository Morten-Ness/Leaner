import Mathlib

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem trace_eq_neg_charpoly_nextCoeff (M : Matrix n n R) : M.trace = -M.charpoly.nextCoeff := by
  cases isEmpty_or_nonempty n
  · simp [nextCoeff]
  nontriviality
  simp [Matrix.trace_eq_neg_charpoly_coeff, nextCoeff]

set_option backward.isDefEq.respectTransparency false in

