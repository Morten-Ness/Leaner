import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reverse_zero : Polynomial.reverse (0 : R[X]) = 0 := rfl

