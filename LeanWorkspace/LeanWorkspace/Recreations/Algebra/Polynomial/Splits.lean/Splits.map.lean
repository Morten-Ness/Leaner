import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.map {f : R[X]} (hf : Polynomial.Splits f) {S : Type*} [Semiring S] (i : R →+* S) :
    Polynomial.Splits (map i f) := by
  induction hf using Submonoid.closure_induction <;> aesop

