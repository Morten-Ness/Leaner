import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_le_trailingDegree : ↑(Polynomial.natTrailingDegree p) ≤ Polynomial.trailingDegree p := ENat.coe_toNat_le_self _

