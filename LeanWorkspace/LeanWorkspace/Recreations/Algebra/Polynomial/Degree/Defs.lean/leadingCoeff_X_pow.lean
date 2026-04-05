import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_X_pow (n : ℕ) : Polynomial.leadingCoeff ((Polynomial.X : R[X]) ^ n) = 1 := by
  simpa only [C_1, one_mul] using Polynomial.leadingCoeff_C_mul_X_pow (1 : R) n

