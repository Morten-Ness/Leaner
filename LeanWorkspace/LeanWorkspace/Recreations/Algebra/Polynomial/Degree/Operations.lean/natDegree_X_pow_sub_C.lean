import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

variable [Nontrivial R]

theorem natDegree_X_pow_sub_C {n : ℕ} {r : R} : (Polynomial.X ^ n - Polynomial.C r).natDegree = n := by
  rw [sub_eq_add_neg, ← map_neg Polynomial.C r, Polynomial.natDegree_X_pow_add_C]

