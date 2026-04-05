import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_eq_of_natDegree_add_lt_left (p q : R[X])
    (H : natDegree (p + q) < natDegree p) : natDegree p = natDegree q := by
  by_contra h
  cases Nat.lt_or_lt_of_ne h with
  | inl h => exact lt_asymm h (by rwa [Polynomial.natDegree_add_eq_right_of_natDegree_lt h] at H)
  | inr h =>
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt h] at H
    exact LT.lt.false H

