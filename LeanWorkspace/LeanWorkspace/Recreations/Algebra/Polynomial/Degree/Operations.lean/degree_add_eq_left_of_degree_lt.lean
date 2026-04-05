import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q) = degree p := le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _) <|
    degree_le_degree <| by
      rw [coeff_add, Polynomial.coeff_natDegree_eq_zero_of_degree_lt h, add_zero]
      exact mt leadingCoeff_eq_zero.1 (Polynomial.ne_zero_of_degree_gt h)

