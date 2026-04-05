import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem as_sum_range' (p : R[X]) (n : ℕ) (hn : p.natDegree < n) :
    p = ∑ i ∈ range n, monomial i (coeff p i) := p.sum_monomial_eq.symm.trans <| Polynomial.sum_over_range' p monomial_zero_right _ hn

