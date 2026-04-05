import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_eval_one : p.mirror.eval 1 = p.eval 1 := by
  simp_rw [eval_eq_sum_range, one_pow, mul_one, Polynomial.mirror_natDegree]
  refine Finset.sum_bij_ne_zero ?_ ?_ ?_ ?_ ?_
  · exact fun n _ _ => revAt (p.natDegree + p.natTrailingDegree) n
  · intro n hn hp
    rw [Finset.mem_range_succ_iff] at *
    rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
    rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right, ← Polynomial.mirror_natTrailingDegree]
    exact natTrailingDegree_le_of_ne_zero hp
  · exact fun n₁ _ _ _ _ _ h => by rw [← @revAt_invol _ n₁, h, revAt_invol]
  · intro n hn hp
    use revAt (p.natDegree + p.natTrailingDegree) n
    refine ⟨?_, ?_, revAt_invol⟩
    · rw [Finset.mem_range_succ_iff] at *
      rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
      rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right]
      exact natTrailingDegree_le_of_ne_zero hp
    · change p.mirror.coeff _ ≠ 0
      rwa [Polynomial.coeff_mirror, revAt_invol]
  · exact fun n _ _ => Polynomial.coeff_mirror p n

