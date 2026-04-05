import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q := by
  rw [add_comm, Polynomial.degree_add_eq_left_of_degree_lt h]

