import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p := by
  rw [← Polynomial.degree_neg q] at h
  rw [sub_eq_add_neg, Polynomial.degree_add_eq_left_of_degree_lt h]

