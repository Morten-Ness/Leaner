import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem coeff_X_sub_C_mul {p : R[X]} {r : R} {a : ℕ} :
    coeff ((Polynomial.X - Polynomial.C r) * p) (a + 1) = coeff p a - r * coeff p (a + 1) := by simp [sub_mul]

