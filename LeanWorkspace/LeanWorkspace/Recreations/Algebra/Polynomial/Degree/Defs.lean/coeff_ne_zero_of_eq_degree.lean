import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_ne_zero_of_eq_degree (hn : Polynomial.degree p = n) : coeff p n ≠ 0 := fun h =>
  mem_support_iff.mp (mem_of_max hn) h

