import Mathlib

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem mem_spectrum_iff_isRoot_charpoly {r : K} : r ∈ spectrum K A ↔ IsRoot A.charpoly r := by
  simp [eval_charpoly, spectrum.mem_iff, isUnit_iff_isUnit_det, algebraMap_eq_diagonal,
    Pi.algebraMap_def]

