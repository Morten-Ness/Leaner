import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem coeff_mul_X_sub_C {p : R[X]} {r : R} {a : ℕ} :
    coeff (p * (Polynomial.X - Polynomial.C r)) (a + 1) = coeff p a - coeff p (a + 1) * r := by simp [mul_sub]

