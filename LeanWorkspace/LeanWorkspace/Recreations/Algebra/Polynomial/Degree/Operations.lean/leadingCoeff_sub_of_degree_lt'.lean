import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem leadingCoeff_sub_of_degree_lt' (h : Polynomial.degree p < Polynomial.degree q) :
    (p - q).leadingCoeff = -q.leadingCoeff := by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg, Polynomial.leadingCoeff_add_of_degree_lt h, leadingCoeff_neg]

