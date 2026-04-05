import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_ne_C [Nontrivial R] (a : R) : Polynomial.X ≠ Polynomial.C a := by
  intro he
  simpa using Polynomial.monomial_eq_monomial_iff.1 he

