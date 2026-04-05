import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_mul_natTrailingDegree_add_natTrailingDegree : (p * q).coeff
    (p.natTrailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff := by
  rw [coeff_mul]
  refine
    Finset.sum_eq_single (p.natTrailingDegree, q.natTrailingDegree) ?_ fun h =>
      (h (mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [mem_antidiagonal] at h₁
  by_cases! hi : i < p.natTrailingDegree
  · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
  by_cases! hj : j < q.natTrailingDegree
  · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj, mul_zero]
  refine (h₂ (Prod.ext_iff.mpr ?_).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm

