import Mathlib

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem isNilpotent_trace_of_isNilpotent (hM : IsNilpotent M) :
    IsNilpotent (trace M) := by
  cases isEmpty_or_nonempty n
  · simp
  suffices IsNilpotent (coeff (Matrix.charpolyRev M) 1) by simpa using this
  exact (isUnit_iff_coeff_isUnit_isNilpotent.mp (Matrix.isUnit_charpolyRev_of_isNilpotent hM)).2
    _ one_ne_zero

