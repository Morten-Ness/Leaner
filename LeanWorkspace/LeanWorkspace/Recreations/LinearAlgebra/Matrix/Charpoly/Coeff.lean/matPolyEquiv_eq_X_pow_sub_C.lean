import Mathlib

open scoped Ring Polynomial

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

set_option backward.isDefEq.respectTransparency false in
theorem matPolyEquiv_eq_X_pow_sub_C {K : Type*} (k : ℕ) [CommRing K] (M : Matrix n n K) :
    matPolyEquiv ((expand K k : K[X] →+* K[X]).mapMatrix (Matrix.charmatrix (M ^ k))) =
      Polynomial.X ^ k - Polynomial.C (M ^ k) := by
  ext m i j
  rw [coeff_sub, coeff_C, matPolyEquiv_coeff_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AlgHom.coe_toRingHom, coeff_X_pow]
  by_cases hij : i = j
  · rw [hij, Matrix.charmatrix_apply_eq, map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow, coeff_C]
    split_ifs with mp m0 <;> simp
  · rw [Matrix.charmatrix_apply_ne _ _ _ hij, map_neg, expand_C, coeff_neg, coeff_C]
    split_ifs with m0 mp <;> simp_all

