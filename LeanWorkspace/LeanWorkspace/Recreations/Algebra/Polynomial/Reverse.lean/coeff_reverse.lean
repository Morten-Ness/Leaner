import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem coeff_reverse (f : R[X]) (n : ℕ) : f.reverse.coeff n = f.coeff (Polynomial.revAt f.natDegree n) := by
  rw [Polynomial.reverse, Polynomial.coeff_reflect]

