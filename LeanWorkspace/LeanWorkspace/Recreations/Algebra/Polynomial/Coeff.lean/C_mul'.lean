import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem C_mul' (a : R) (f : R[X]) : Polynomial.C a * f = a • f := by
  ext
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_smul, smul_eq_mul]

