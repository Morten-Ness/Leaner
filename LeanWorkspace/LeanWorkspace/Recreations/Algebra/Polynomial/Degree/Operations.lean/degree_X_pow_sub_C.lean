import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

variable [Nontrivial R]

theorem degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((Polynomial.X : R[X]) ^ n - Polynomial.C a) = n := by
  rw [sub_eq_add_neg, ← map_neg Polynomial.C a, Polynomial.degree_X_pow_add_C hn]

