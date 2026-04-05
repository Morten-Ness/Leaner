import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_eq_of_degree_eq_some {p : R[X]} {n : ℕ} (h : Polynomial.degree p = n) : Polynomial.natDegree p = n := by
  rw [Polynomial.natDegree, h, Nat.cast_withBot, WithBot.unbotD_coe]

