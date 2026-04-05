import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.C_mul {f : R[X]} (hf : Polynomial.Splits f) (a : R) : Polynomial.Splits (C a * f) := (Polynomial.Splits.C a).mul hf

