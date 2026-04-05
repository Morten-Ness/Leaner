import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

theorem trinomial_leading_coeff' (hkm : k < m) (hmn : m < n) :
    (Polynomial.trinomial k m n u v w).coeff n = w := by
  rw [Polynomial.trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_neg (hkm.trans hmn).ne', if_neg hmn.ne', if_pos rfl, zero_add, zero_add]

