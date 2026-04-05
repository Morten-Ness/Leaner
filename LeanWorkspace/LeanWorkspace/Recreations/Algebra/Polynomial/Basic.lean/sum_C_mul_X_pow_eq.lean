import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fun n a => Polynomial.C a * Polynomial.X ^ n) = p := by
  simp_rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.sum_monomial_eq]

