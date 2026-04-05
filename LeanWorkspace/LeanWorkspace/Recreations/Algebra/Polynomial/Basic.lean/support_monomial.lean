import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_monomial (n) {a : R} (H : a ≠ 0) : (Polynomial.monomial n a).support = singleton n := by
  rw [← Polynomial.ofFinsupp_single, Polynomial.support]; exact Finsupp.support_single_ne_zero _ H

