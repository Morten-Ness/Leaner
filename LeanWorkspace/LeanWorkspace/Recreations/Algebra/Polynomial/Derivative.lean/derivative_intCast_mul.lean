import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R]

theorem derivative_intCast_mul {n : ℤ} {f : R[X]} : Polynomial.derivative ((n : R[X]) * f) =
    n * Polynomial.derivative f := by
  simp

