import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem natTrailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, Polynomial.trailingCoeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, Polynomial.trailingCoeff_zero, mul_zero])
  apply Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some
  rw [Polynomial.trailingDegree_mul' h, Nat.cast_withTop (Polynomial.natTrailingDegree p + Polynomial.natTrailingDegree q),
    WithTop.coe_add, ← Nat.cast_withTop, ← Nat.cast_withTop,
    ← Polynomial.trailingDegree_eq_natTrailingDegree hp, ← Polynomial.trailingDegree_eq_natTrailingDegree hq]

