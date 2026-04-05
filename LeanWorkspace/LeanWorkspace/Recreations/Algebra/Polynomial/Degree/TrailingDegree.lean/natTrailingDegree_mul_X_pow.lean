import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_mul_X_pow {p : R[X]} (hp : p ≠ 0) (n : ℕ) :
    (p * Polynomial.X ^ n).natTrailingDegree = p.natTrailingDegree + n := by
  apply le_antisymm
  · refine Polynomial.natTrailingDegree_le_of_ne_zero fun h => mt Polynomial.trailingCoeff_eq_zero.mp hp ?_
    rwa [Polynomial.trailingCoeff, ← coeff_mul_X_pow]
  · rw [Polynomial.natTrailingDegree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n ≤ y := by
      rw [mem_support_iff, coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff, coeff_mul_X_pow', if_pos key] at hy
    exact (le_tsub_iff_right key).mp (Polynomial.natTrailingDegree_le_of_ne_zero hy)

