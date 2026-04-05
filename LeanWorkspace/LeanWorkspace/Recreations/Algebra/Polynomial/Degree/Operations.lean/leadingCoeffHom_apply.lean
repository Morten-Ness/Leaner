import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

variable [NoZeroDivisors R] {p q : R[X]}

theorem leadingCoeffHom_apply (p : R[X]) : Polynomial.leadingCoeffHom p = leadingCoeff p := rfl

