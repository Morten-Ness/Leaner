import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

theorem nextCoeff_C_eq_zero (c : R) : Polynomial.nextCoeff (Polynomial.C c) = 0 := by
  rw [Polynomial.nextCoeff]
  simp

