import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_sub_C (hp : 0 < degree p) : degree (p - Polynomial.C a) = degree p := by
  rw [sub_eq_add_neg, ← C_neg, Polynomial.degree_add_C hp]

