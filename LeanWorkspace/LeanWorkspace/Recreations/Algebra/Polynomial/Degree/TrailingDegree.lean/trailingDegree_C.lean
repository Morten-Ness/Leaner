import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_C (ha : a ≠ 0) : Polynomial.trailingDegree (Polynomial.C a) = (0 : ℕ∞) := Polynomial.trailingDegree_monomial ha

