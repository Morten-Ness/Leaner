import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem as_sum_range_C_mul_X_pow' (p : R[X]) {n : ℕ} (hn : p.natDegree < n) :
    p = ∑ i ∈ range n, Polynomial.C (coeff p i) * Polynomial.X ^ i := (Polynomial.as_sum_range' p _ hn).trans <| by simp only [C_mul_X_pow_eq_monomial]

