import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem coeff_divByMonic_X_sub_C (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (Polynomial.X - Polynomial.C a)).coeff n = ∑ i ∈ Icc (n + 1) p.natDegree, a ^ (i - (n + 1)) * p.coeff i := by
  wlog h : p.natDegree ≤ n generalizing n
  · refine Nat.decreasingInduction' (fun n hn _ ih ↦ ?_) (le_of_not_ge h) ?_
    · rw [Polynomial.coeff_divByMonic_X_sub_C_rec, ih, eq_comm, Icc_eq_cons_Ioc (Nat.succ_le_iff.mpr hn),
          sum_cons, Nat.sub_self, pow_zero, one_mul, mul_sum]
      congr 1; refine Finset.sum_congr ?_ fun i hi ↦ ?_
      · ext; simp
      rw [← mul_assoc, ← pow_succ', eq_comm, i.sub_succ', Nat.sub_add_cancel]
      apply Nat.le_sub_of_add_le
      rw [add_comm]; exact (mem_Icc.mp hi).1
    · exact this _ le_rfl
  rw [Icc_eq_empty (Nat.lt_succ_iff.mpr h).not_ge, sum_empty]
  nontriviality R
  by_cases hp : p.natDegree = 0
  · rw [(Polynomial.divByMonic_eq_zero_iff <| Polynomial.monic_X_sub_C a).mpr, coeff_zero]
    apply degree_lt_degree; rw [hp, Polynomial.natDegree_X_sub_C]; simp
  · apply coeff_eq_zero_of_natDegree_lt
    rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C a), Polynomial.natDegree_X_sub_C]
    exact (Nat.pred_lt hp).trans_le h

