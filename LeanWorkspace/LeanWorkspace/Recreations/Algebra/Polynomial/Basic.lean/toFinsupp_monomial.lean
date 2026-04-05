import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_monomial (n : ℕ) (r : R) : (Polynomial.monomial n r).toFinsupp = .single n r := by
  simp [Polynomial.monomial]

