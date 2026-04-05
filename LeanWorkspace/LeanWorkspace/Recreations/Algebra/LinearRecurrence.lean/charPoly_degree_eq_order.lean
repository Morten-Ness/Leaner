import Mathlib

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

theorem charPoly_degree_eq_order [Nontrivial R] : (LinearRecurrence.charPoly E).degree = E.order := by
  rw [LinearRecurrence.charPoly, degree_sub_eq_left_of_degree_lt]
    <;> rw [degree_monomial E.order one_ne_zero]
  simp_rw [← C_mul_X_pow_eq_monomial]
  exact degree_sum_fin_lt E.coeffs

