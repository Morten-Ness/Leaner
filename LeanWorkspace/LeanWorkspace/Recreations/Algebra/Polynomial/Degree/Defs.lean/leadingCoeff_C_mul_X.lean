import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_C_mul_X (a : R) : Polynomial.leadingCoeff (Polynomial.C a * Polynomial.X) = a := by
  simpa only [pow_one] using Polynomial.leadingCoeff_C_mul_X_pow a 1

