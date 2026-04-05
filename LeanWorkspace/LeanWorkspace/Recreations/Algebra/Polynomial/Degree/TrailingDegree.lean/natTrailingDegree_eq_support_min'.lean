import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem natTrailingDegree_eq_support_min' (h : p ≠ 0) :
    Polynomial.natTrailingDegree p = p.support.min' (nonempty_support_iff.mpr h) := by
  rw [Polynomial.natTrailingDegree, Polynomial.trailingDegree, ← Finset.coe_min', ENat.some_eq_coe, ENat.toNat_coe]

