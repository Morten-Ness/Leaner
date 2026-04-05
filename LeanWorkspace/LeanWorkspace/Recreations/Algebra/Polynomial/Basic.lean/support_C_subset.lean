import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_C_subset (a : R) : (Polynomial.C a).support ⊆ singleton 0 := Polynomial.support_monomial' 0 a

