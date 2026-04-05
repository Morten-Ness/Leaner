import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.mul {f g : R[X]} (hf : Polynomial.Splits f) (hg : Polynomial.Splits g) :
    Polynomial.Splits (f * g) := mul_mem hf hg

