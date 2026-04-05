import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 := Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

