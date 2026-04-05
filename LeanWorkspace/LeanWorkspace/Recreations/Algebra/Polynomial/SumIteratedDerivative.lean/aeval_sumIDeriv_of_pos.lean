import Mathlib

open scoped Nat

variable {R S : Type*}

variable [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]

theorem aeval_sumIDeriv_of_pos [Nontrivial A] [NoZeroDivisors A] (p : R[X]) {q : ℕ} (hq : 0 < q)
    (inj_amap : Function.Injective (algebraMap R A)) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
      ∀ (r : A) {p' : A[X]},
        p.map (algebraMap R A) = (X - C r) ^ (q - 1) * p' →
        aeval r (Polynomial.sumIDeriv p) = (q - 1)! • p'.eval r + q ! • aeval r gp := by
  rcases eq_or_ne p 0 with (rfl | p0)
  · use 0
    rw [natDegree_zero]
    use Nat.zero_le _
    intro r p' hp
    rw [map_zero, map_zero, smul_zero, add_zero]
    rw [Polynomial.map_zero] at hp
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left ?_
    · rw [hp, eval_zero, smul_zero]
    exact fun h => X_sub_C_ne_zero r (eq_zero_of_pow_eq_zero h)
  let c k := if hk : q ≤ k then (Polynomial.aeval_iterate_derivative_of_ge A p q hk).choose else 0
  have c_le (k) : (c k).natDegree ≤ p.natDegree - k := by
    dsimp only [c]
    split_ifs with h
    · exact (Polynomial.aeval_iterate_derivative_of_ge A p q h).choose_spec.1
    · rw [natDegree_zero]; exact Nat.zero_le _
  have hc (k) (hk : q ≤ k) : ∀ (r : A), aeval r (derivative^[k] p) = q ! • aeval r (c k) := by
    simp_rw [c, dif_pos hk]
    exact (Polynomial.aeval_iterate_derivative_of_ge A p q hk).choose_spec.2
  refine ⟨∑ x ∈ Ico q (p.natDegree + 1), c x, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i hi => (c_le i).trans (tsub_le_tsub_left (mem_Ico.mp hi).1 _)⟩
  intro r p' hp
  have : range (p.natDegree + 1) = range q ∪ Ico q (p.natDegree + 1) := by
    rw [range_eq_Ico, Ico_union_Ico_eq_Ico hq.le]
    rw [← tsub_le_iff_right]
    calc
      q - 1 ≤ q - 1 + p'.natDegree := le_self_add
      _ = (p.map <| algebraMap R A).natDegree := by
        rw [hp, natDegree_mul, natDegree_pow, natDegree_X_sub_C, mul_one,
          ← Nat.sub_add_comm (Nat.one_le_of_lt hq)]
        · exact pow_ne_zero _ (X_sub_C_ne_zero r)
        · rintro rfl
          rw [mul_zero, Polynomial.map_eq_zero_iff inj_amap] at hp
          exact p0 hp
      _ ≤ p.natDegree := natDegree_map_le
  rw [← zero_add ((q - 1)! • p'.eval r)]
  rw [Polynomial.sumIDeriv_apply, map_sum, map_sum, this]
  have : range q = range (q - 1 + 1) := by rw [tsub_add_cancel_of_le (Nat.one_le_of_lt hq)]
  rw [sum_union, this, sum_range_succ]
  · congr 2
    · apply sum_eq_zero
      exact fun x hx => Polynomial.aeval_iterate_derivative_of_lt p _ r hp (mem_range.mp hx)
    · rw [← Polynomial.aeval_iterate_derivative_self _ _ _ hp]
    · rw [smul_sum, Finset.sum_congr rfl]
      intro k hk
      exact hc k (mem_Ico.mp hk).1 r
  · rw [range_eq_Ico, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_inter, mem_Ico, mem_Ico] at hx
    exact hx.1.2.not_ge hx.2.1

