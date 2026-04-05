import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_lt_wf : WellFounded fun p q : R[X] => Polynomial.trailingDegree p < Polynomial.trailingDegree q := InvImage.wf Polynomial.trailingDegree wellFounded_lt

