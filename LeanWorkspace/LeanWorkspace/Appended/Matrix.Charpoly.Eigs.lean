import Mathlib

section

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem det_eq_prod_roots_charpoly [IsAlgClosed K] : A.det = (Matrix.charpoly A).roots.prod := Matrix.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)

end

section

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem trace_eq_sum_roots_charpoly [IsAlgClosed K] : A.trace = (Matrix.charpoly A).roots.sum := Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)

end
