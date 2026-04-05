import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_add (f g : R[X]) (N : ℕ) : Polynomial.reflect N (f + g) = Polynomial.reflect N f + Polynomial.reflect N g := by
  ext
  simp only [coeff_add, Polynomial.coeff_reflect]

