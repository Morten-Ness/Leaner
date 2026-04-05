import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_natCast {n : ℕ} : Polynomial.derivative (n : R[X]) = 0 := by
  rw [← map_natCast Polynomial.C n]
  exact Polynomial.derivative_C

