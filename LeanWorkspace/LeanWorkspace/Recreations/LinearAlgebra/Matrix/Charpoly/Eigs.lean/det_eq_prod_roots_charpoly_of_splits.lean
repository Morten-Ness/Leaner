import Mathlib

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem det_eq_prod_roots_charpoly_of_splits (hAps : A.charpoly.Splits) :
    A.det = (Matrix.charpoly A).roots.prod := by
  rw [det_eq_sign_charpoly_coeff, ← charpoly_natDegree_eq_dim A,
    hAps.coeff_zero_eq_prod_roots_of_monic A.charpoly_monic, ← mul_assoc,
    ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul]

