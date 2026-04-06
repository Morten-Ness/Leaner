FAIL
import Mathlib

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R K : Type*} [CommRing R] [Field K]

variable {A : Matrix n n K} {B : Matrix n n R}

theorem det_eq_prod_roots_charpoly [IsAlgClosed K] : A.det = (Matrix.charpoly A).roots.prod := by
  rw [Matrix.det_eq_sign_charpoly_coeff]
  have hmonic : (Matrix.charpoly A).Monic := Matrix.charpoly_monic A
  have hsplit : (Matrix.charpoly A).Splits (RingHom.id K) := by
    exact IsAlgClosed.splits_codomain (Matrix.charpoly A)
  rw [hmonic.coeff_zero_eq_prod_roots hsplit]
  simp
