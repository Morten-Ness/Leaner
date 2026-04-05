import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.one : Polynomial.Splits (1 : R[X]) := Polynomial.Splits.C (1 : R)

