import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

variable [Nontrivial R]

theorem leadingCoeff_X_sub_C [Ring S] (r : S) : (Polynomial.X - Polynomial.C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg Polynomial.C r, Polynomial.leadingCoeff_X_add_C]

