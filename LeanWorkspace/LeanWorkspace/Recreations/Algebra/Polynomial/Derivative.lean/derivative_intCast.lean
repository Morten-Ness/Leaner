import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R]

theorem derivative_intCast {n : ℤ} : Polynomial.derivative (n : R[X]) = 0 := by
  rw [← Polynomial.C_eq_intCast n]
  exact Polynomial.derivative_C

