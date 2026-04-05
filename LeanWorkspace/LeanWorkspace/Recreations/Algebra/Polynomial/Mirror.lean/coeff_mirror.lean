import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem coeff_mirror (n : ℕ) :
    p.mirror.coeff n = p.coeff (revAt (p.natDegree + p.natTrailingDegree) n) := by
  by_cases h2 : p.natDegree < n
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [Polynomial.mirror_natDegree])]
    by_cases h1 : n ≤ p.natDegree + p.natTrailingDegree
    · rw [revAt_le h1, coeff_eq_zero_of_lt_natTrailingDegree]
      exact (tsub_lt_iff_left h1).mpr (Nat.add_lt_add_right h2 _)
    · rw [← revAtFun_eq, revAtFun, if_neg h1, coeff_eq_zero_of_natDegree_lt h2]
  rw [not_lt] at h2
  rw [revAt_le (h2.trans (Nat.le_add_right _ _))]
  by_cases h3 : p.natTrailingDegree ≤ n
  · rw [← tsub_add_eq_add_tsub h2, ← tsub_tsub_assoc h2 h3, Polynomial.mirror, coeff_mul_X_pow', if_pos h3,
      coeff_reverse, revAt_le (tsub_le_self.trans h2)]
  rw [not_le] at h3
  rw [coeff_eq_zero_of_natDegree_lt (lt_tsub_iff_right.mpr (Nat.add_lt_add_left h3 _))]
  exact coeff_eq_zero_of_lt_natTrailingDegree (by rwa [Polynomial.mirror_natTrailingDegree])

--TODO: Extract `Finset.sum_range_rev_at` lemma.

