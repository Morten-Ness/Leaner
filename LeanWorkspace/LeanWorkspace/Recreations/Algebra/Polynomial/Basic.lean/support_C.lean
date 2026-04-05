import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_C {a : R} (h : a ≠ 0) : (Polynomial.C a).support = singleton 0 := Polynomial.support_monomial 0 h

