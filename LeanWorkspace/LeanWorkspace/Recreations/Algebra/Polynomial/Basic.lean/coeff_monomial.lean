import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_monomial : Polynomial.coeff (Polynomial.monomial n a) m = if n = m then a else 0 := by
  simp [Polynomial.coeff, Finsupp.single_apply]

