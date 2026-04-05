import Mathlib

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem matPolyEquiv_eq_X_pow_sub_C {K : Type*} (k : ℕ) [CommRing K] (M : Matrix n n K) :
    matPolyEquiv ((expand K k : K[X] →+* K[X]).mapMatrix (charmatrix (M ^ k))) =
      X ^ k - C (M ^ k) := by
  ext m i j
  rw [coeff_sub, coeff_C, matPolyEquiv_coeff_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AlgHom.coe_toRingHom, coeff_X_pow]
  by_cases hij : i = j
  · rw [hij, charmatrix_apply_eq, map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow, coeff_C]
    split_ifs with mp m0 <;> simp
  · rw [charmatrix_apply_ne _ _ _ hij, map_neg, expand_C, coeff_neg, coeff_C]
    split_ifs with m0 mp <;> simp_all

