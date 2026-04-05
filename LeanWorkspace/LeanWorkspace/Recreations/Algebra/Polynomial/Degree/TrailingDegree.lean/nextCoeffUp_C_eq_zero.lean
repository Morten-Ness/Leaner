import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R]

theorem nextCoeffUp_C_eq_zero (c : R) : Polynomial.nextCoeffUp (Polynomial.C c) = 0 := by
  rw [Polynomial.nextCoeffUp]
  simp

