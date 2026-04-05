import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R]

theorem derivative_X_sub_C (c : R) : Polynomial.derivative (Polynomial.X - Polynomial.C c) = 1 := by
  rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero]

