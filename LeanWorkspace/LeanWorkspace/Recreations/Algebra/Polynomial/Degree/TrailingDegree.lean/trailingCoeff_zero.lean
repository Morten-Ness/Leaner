import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingCoeff_zero : Polynomial.trailingCoeff (0 : R[X]) = 0 := rfl

