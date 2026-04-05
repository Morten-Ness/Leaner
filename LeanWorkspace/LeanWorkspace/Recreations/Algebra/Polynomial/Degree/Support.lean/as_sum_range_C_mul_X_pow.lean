import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem as_sum_range_C_mul_X_pow (p : R[X]) :
    p = ∑ i ∈ range (p.natDegree + 1), Polynomial.C (coeff p i) * Polynomial.X ^ i := Polynomial.as_sum_range_C_mul_X_pow' p (lt_add_one _)

