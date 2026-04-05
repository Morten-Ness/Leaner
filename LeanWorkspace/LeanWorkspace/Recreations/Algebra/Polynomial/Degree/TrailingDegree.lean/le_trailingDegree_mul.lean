import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem le_trailingDegree_mul : p.trailingDegree + q.trailingDegree ≤ (p * q).trailingDegree := by
  refine Finset.le_min fun n hn => ?_
  rw [mem_support_iff, coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans_eq ?_
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← mem_antidiagonal]

