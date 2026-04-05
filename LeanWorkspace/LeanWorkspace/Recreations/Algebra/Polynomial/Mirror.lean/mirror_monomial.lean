import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = monomial n a := by
  classical
    by_cases ha : a = 0
    · rw [ha, monomial_zero_right, Polynomial.mirror_zero]
    · rw [Polynomial.mirror, reverse, natDegree_monomial n a, if_neg ha, natTrailingDegree_monomial ha, ←
        C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, revAt_le (le_refl n), tsub_self, pow_zero,
        mul_one]

