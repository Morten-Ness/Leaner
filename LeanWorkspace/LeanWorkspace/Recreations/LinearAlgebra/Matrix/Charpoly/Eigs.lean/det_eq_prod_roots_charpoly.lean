import Mathlib

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem det_eq_prod_roots_charpoly [IsAlgClosed K] : A.det = (Matrix.charpoly A).roots.prod := Matrix.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)

