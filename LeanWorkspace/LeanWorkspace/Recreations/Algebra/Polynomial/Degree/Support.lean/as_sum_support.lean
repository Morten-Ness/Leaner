import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem as_sum_support (p : R[X]) : p = ∑ i ∈ p.support, monomial i (p.coeff i) := (sum_monomial_eq p).symm

