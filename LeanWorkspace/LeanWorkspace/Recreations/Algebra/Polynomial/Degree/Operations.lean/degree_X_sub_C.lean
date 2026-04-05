import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

variable [Nontrivial R]

theorem degree_X_sub_C (a : R) : degree (Polynomial.X - Polynomial.C a) = 1 := by
  rw [sub_eq_add_neg, ← map_neg Polynomial.C a, Polynomial.degree_X_add_C]

