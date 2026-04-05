import Mathlib

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem trace_eq_sum_roots_charpoly_of_splits (hAps : A.charpoly.Splits) :
    A.trace = (Matrix.charpoly A).roots.sum := by
  rcases isEmpty_or_nonempty n with h | _
  · simp
  · rw [trace_eq_neg_charpoly_nextCoeff, neg_eq_iff_eq_neg,
      ← hAps.nextCoeff_eq_neg_sum_roots_of_monic A.charpoly_monic]

