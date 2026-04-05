import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem degree_eq_zero_of_isUnit [Nontrivial R] (h : IsUnit p) : degree p = 0 := (natDegree_eq_zero_iff_degree_le_zero.mp <| Polynomial.natDegree_eq_zero_of_isUnit h).antisymm
    (zero_le_degree_iff.mpr h.ne_zero)

