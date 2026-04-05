import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem degree_eq_of_le_of_coeff_ne_zero (pn : p.degree ≤ n) (p1 : p.coeff n ≠ 0) : p.degree = n := pn.antisymm (le_degree_of_ne_zero p1)

