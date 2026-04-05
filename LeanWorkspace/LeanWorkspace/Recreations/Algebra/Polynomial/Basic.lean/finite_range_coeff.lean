import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem finite_range_coeff (f : R[X]) : (Set.range f.coeff).Finite := Finsupp.finite_range _

