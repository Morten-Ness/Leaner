import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

theorem trinomial_middle_coeff (hkm : k < m) (hmn : m < n) :
    (Polynomial.trinomial k m n u v w).coeff m = v := by
  rw [Polynomial.trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_neg hkm.ne', if_pos rfl, if_neg hmn.ne, zero_add, add_zero]

