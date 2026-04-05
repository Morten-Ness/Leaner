import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q := by
  rw [← Polynomial.degree_neg q] at h
  rw [sub_eq_add_neg, Polynomial.degree_add_eq_right_of_degree_lt h, Polynomial.degree_neg]

