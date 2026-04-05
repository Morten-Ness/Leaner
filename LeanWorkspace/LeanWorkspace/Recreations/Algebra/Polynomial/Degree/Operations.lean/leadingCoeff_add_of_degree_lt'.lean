import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_add_of_degree_lt' (h : degree q < degree p) :
    leadingCoeff (p + q) = leadingCoeff p := by
  rw [add_comm]
  exact Polynomial.leadingCoeff_add_of_degree_lt h

