import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem leadingCoeff_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} :
    (Polynomial.X ^ n - Polynomial.C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg Polynomial.C r, Polynomial.leadingCoeff_X_pow_add_C hn]

