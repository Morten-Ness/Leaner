import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, Polynomial.trailingCoeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, Polynomial.trailingCoeff_zero, mul_zero])
  refine le_antisymm ?_ Polynomial.le_trailingDegree_mul
  rw [Polynomial.trailingDegree_eq_natTrailingDegree hp, Polynomial.trailingDegree_eq_natTrailingDegree hq, ←
    ENat.coe_add]
  apply Polynomial.trailingDegree_le_of_ne_zero
  rwa [Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree]

