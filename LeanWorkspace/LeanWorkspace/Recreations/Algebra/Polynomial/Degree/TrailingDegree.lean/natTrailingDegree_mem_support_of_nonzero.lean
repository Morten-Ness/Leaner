import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_mem_support_of_nonzero : p ≠ 0 → Polynomial.natTrailingDegree p ∈ p.support := mem_support_iff.mpr ∘ Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr

