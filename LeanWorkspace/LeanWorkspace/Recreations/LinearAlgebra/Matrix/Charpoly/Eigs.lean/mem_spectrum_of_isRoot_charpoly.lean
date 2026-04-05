import Mathlib

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem mem_spectrum_of_isRoot_charpoly [Nontrivial R]
    {r : R} (hr : IsRoot B.charpoly r) : r ∈ spectrum R B := by
  simp_all [eval_charpoly, spectrum.mem_iff, isUnit_iff_isUnit_det, algebraMap_eq_diagonal,
    Pi.algebraMap_def]

