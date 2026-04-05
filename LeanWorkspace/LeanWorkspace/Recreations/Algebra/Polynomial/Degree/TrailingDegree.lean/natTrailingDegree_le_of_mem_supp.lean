import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_le_of_mem_supp (a : ℕ) : a ∈ p.support → Polynomial.natTrailingDegree p ≤ a := Polynomial.natTrailingDegree_le_of_ne_zero ∘ mem_support_iff.mp

