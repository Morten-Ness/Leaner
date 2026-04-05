import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_C_mul_X_pow (a : R) (n : ℕ) : Polynomial.leadingCoeff (Polynomial.C a * Polynomial.X ^ n) = a := by
  rw [C_mul_X_pow_eq_monomial, Polynomial.leadingCoeff_monomial]

