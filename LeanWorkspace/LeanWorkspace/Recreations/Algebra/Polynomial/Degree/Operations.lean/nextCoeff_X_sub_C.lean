import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

variable [Nontrivial R]

theorem nextCoeff_X_sub_C [Ring S] (c : S) : nextCoeff (Polynomial.X - Polynomial.C c) = -c := by
  rw [sub_eq_add_neg, ← map_neg Polynomial.C c, Polynomial.nextCoeff_X_add_C]

