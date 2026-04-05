import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem le_natTrailingDegree_mul (h : p * q ≠ 0) :
    p.natTrailingDegree + q.natTrailingDegree ≤ (p * q).natTrailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, mul_zero])
  rw [← WithTop.coe_le_coe, WithTop.coe_add, ← Nat.cast_withTop (Polynomial.natTrailingDegree p),
    ← Nat.cast_withTop (Polynomial.natTrailingDegree q), ← Nat.cast_withTop (Polynomial.natTrailingDegree (p * q)),
    ← Polynomial.trailingDegree_eq_natTrailingDegree hp, ← Polynomial.trailingDegree_eq_natTrailingDegree hq,
    ← Polynomial.trailingDegree_eq_natTrailingDegree h]
  exact Polynomial.le_trailingDegree_mul

