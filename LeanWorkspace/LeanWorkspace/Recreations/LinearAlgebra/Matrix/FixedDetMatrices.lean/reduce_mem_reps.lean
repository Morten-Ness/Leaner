import Mathlib

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

variable {m : ℤ}

private theorem reduce_aux {A : Δ m} (h : (A.1 1 0) ≠ 0) :
    |((FixedDetMatrices.reduceStep A).1 1 0)| < |(A.1 1 0)| := by
  suffices ((FixedDetMatrices.reduceStep A).1 1 0) = A.1 0 0 % A.1 1 0 by
    rw [this, abs_eq_self.mpr (Int.emod_nonneg (A.1 0 0) h)]
    exact Int.emod_lt_abs (A.1 0 0) h
  simp_rw [Int.emod_def, sub_eq_add_neg, FixedDetMatrices.reduceStep, FixedDetMatrices.smul_coe, coe_T_zpow, S]
  norm_num [vecMul, vecHead, vecTail, mul_comm]


private theorem A_c_eq_zero {A : Δ m} (ha : A.1 1 0 = 0) : A.1 0 0 * A.1 1 1 = m := by
  simpa only [det_fin_two, ha, mul_zero, sub_zero] using A.2


private theorem A_d_ne_zero {A : Δ m} (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 1 1 ≠ 0 := right_ne_zero_of_mul (A_c_eq_zero (ha) ▸ hm)


private theorem A_a_ne_zero {A : Δ m} (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 0 0 ≠ 0 := left_ne_zero_of_mul (A_c_eq_zero ha ▸ hm)


theorem reduce_mem_reps {m : ℤ} (hm : m ≠ 0) (A : Δ m) : FixedDetMatrices.reduce A ∈ FixedDetMatrices.reps m := by
  induction A using FixedDetMatrices.reduce_rec with
  | step A h1 h2 => simpa only [FixedDetMatrices.reduce_reduceStep h1] using h2
  | base A h =>
    have hd := A_d_ne_zero h hm
    by_cases h1 : 0 < A.1 0 0
    · simp only [FixedDetMatrices.reduce_of_pos h h1]
      have h2 := Int.emod_def (A.1 0 1) (A.1 1 1)
      have h4 := Int.ediv_mul_le (A.1 0 1) hd
      set n : ℤ := A.1 0 1 / A.1 1 1
      have h3 := Int.emod_lt_abs (A.1 0 1) hd
      rw [← abs_eq_self.mpr <| Int.emod_nonneg _ hd] at h3
      simp only [FixedDetMatrices.smul_def, coe_T_zpow]
      suffices A.1 1 0 = 0 ∧ n * A.1 1 0 < A.1 0 0 ∧
          n * A.1 1 1 ≤ A.1 0 1 ∧ |A.1 0 1 + -(n * A.1 1 1)| < |A.1 1 1| by
        simpa only [FixedDetMatrices.reps, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, empty_mul,
          Equiv.symm_apply_apply, Set.mem_setOf_eq, of_apply, cons_val', vecMul, cons_dotProduct,
          vecHead, one_mul, vecTail, Function.comp_apply, Fin.succ_zero_eq_one, neg_mul,
          dotProduct_of_isEmpty, add_zero, zero_mul, zero_add, empty_val', cons_val_fin_one,
          cons_val_one, cons_val_zero, lt_add_neg_iff_add_lt, le_add_neg_iff_add_le]
      simp_all only [mul_comm n, zero_mul, ← sub_eq_add_neg, ← h2,
        Fin.isValue, and_true]
    · simp only [FixedDetMatrices.reps, Fin.isValue, FixedDetMatrices.reduce_of_not_pos h h1, Int.ediv_neg, neg_neg, FixedDetMatrices.smul_def, ←
        mul_assoc, S_mul_S_eq, neg_mul, one_mul, coe_T_zpow, mul_neg, cons_mul, Nat.succ_eq_add_one,
        Nat.reduceAdd, empty_mul, Equiv.symm_apply_apply, neg_of, neg_cons, neg_empty,
        Set.mem_setOf_eq, of_apply, cons_val', Pi.neg_apply, vecMul, cons_dotProduct, vecHead,
        vecTail, Function.comp_apply, Fin.succ_zero_eq_one, h, mul_zero, dotProduct_of_isEmpty,
        add_zero, zero_mul, neg_zero, empty_val', cons_val_fin_one, cons_val_one, cons_val_zero,
        lt_neg, neg_add_rev, zero_add, le_add_neg_iff_add_le, ← le_neg, abs_neg, true_and]
      refine ⟨?_, Int.ediv_mul_le _ hd, ?_⟩
      · simp only [Int.lt_iff_le_and_ne]
        exact ⟨not_lt.mp h1, A_a_ne_zero h hm⟩
      · rw [mul_comm, add_comm, ← Int.sub_eq_add_neg, ← Int.emod_def,
         abs_eq_self.mpr <| Int.emod_nonneg _ hd]
        exact Int.emod_lt_abs _ hd

