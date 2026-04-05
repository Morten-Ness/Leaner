import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.pow {f : R[X]} (hf : Polynomial.Splits f) (n : ℕ) : Polynomial.Splits (f ^ n) := pow_mem hf n

