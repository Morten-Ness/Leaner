import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

variable [Nontrivial R]

theorem X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (Polynomial.X : R[X]) ^ n - Polynomial.C a ≠ 0 := by
  rw [sub_eq_add_neg, ← map_neg Polynomial.C a]
  exact Polynomial.X_pow_add_C_ne_zero hn _

