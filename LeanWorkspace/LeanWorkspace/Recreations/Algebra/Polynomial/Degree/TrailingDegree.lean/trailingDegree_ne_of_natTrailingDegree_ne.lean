import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_ne_of_natTrailingDegree_ne {n : ℕ} :
    p.natTrailingDegree ≠ n → Polynomial.trailingDegree p ≠ n := mt fun h => by rw [Polynomial.natTrailingDegree, h, ENat.toNat_coe]

