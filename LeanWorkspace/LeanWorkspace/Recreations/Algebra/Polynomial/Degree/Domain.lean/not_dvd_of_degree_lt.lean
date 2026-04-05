import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem not_dvd_of_degree_lt (h0 : q ≠ 0) (hl : q.degree < p.degree) : ¬p ∣ q := by
  by_contra hcontra
  exact h0 (Polynomial.eq_zero_of_dvd_of_degree_lt hcontra hl)

