import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_X : Polynomial.leadingCoeff (Polynomial.X : R[X]) = 1 := by
  simpa only [pow_one] using @Polynomial.leadingCoeff_X_pow R _ 1

