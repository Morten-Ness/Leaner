import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ne_zero_of_trailingDegree_lt {n : ℕ∞} (h : Polynomial.trailingDegree p < n) : p ≠ 0 := fun h₀ =>
  h.not_ge (by simp [h₀])

