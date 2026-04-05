import Mathlib

section

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem det_eq_prod_roots_charpoly [IsAlgClosed K] : A.det = (Matrix.charpoly A).roots.prod := Matrix.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)

end

section

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem trace_eq_sum_roots_charpoly [IsAlgClosed K] : A.trace = (Matrix.charpoly A).roots.sum := Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)

end

section

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem trace_eq_sum_roots_charpoly_of_splits (hAps : A.charpoly.Splits) :
    A.trace = (Matrix.charpoly A).roots.sum := by
  rcases isEmpty_or_nonempty n with h | _
  · simp
  · rw [trace_eq_neg_charpoly_nextCoeff, neg_eq_iff_eq_neg,
      ← hAps.nextCoeff_eq_neg_sum_roots_of_monic A.charpoly_monic]

end
