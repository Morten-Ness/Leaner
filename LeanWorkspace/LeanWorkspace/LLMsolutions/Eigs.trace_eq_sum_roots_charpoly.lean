import Mathlib

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem trace_eq_sum_roots_charpoly [IsAlgClosed K] : A.trace = (Matrix.charpoly A).roots.sum := by
  simpa using Matrix.trace_eq_sum_roots_charpoly (A := A)
