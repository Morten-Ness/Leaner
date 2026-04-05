import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem leadingCoeff_sub_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p ≠ leadingCoeff q) :
    leadingCoeff (p - q) = leadingCoeff p - leadingCoeff q := by
  replace h : degree p = degree (-q) := by rwa [q.degree_neg]
  replace hlc : leadingCoeff p + leadingCoeff (-q) ≠ 0 := by
    rwa [← sub_ne_zero, sub_eq_add_neg, ← q.leadingCoeff_neg] at hlc
  rw [sub_eq_add_neg, Polynomial.leadingCoeff_add_of_degree_eq h hlc, leadingCoeff_neg, sub_eq_add_neg]

