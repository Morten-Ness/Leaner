import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem divX_one : Polynomial.divX (1 : R[X]) = 0 := by
  ext
  simpa only [Polynomial.coeff_divX, coeff_zero] using coeff_one

