import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_mul_X_pow {p : R[X]} {n : ℕ} : leadingCoeff (p * Polynomial.X ^ n) = leadingCoeff p := Polynomial.leadingCoeff_mul_monic (monic_X_pow n)

