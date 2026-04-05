import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem as_sum_support_C_mul_X_pow (p : R[X]) : p = ∑ i ∈ p.support, Polynomial.C (p.coeff i) * Polynomial.X ^ i := _root_.trans Polynomial.as_sum_support p <| by simp only [C_mul_X_pow_eq_monomial]

