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


theorem reps_entries_le_m' {A : Δ m} (h : A ∈ FixedDetMatrices.reps m) (i j : Fin 2) :
    A.1 i j ∈ Finset.Icc (-|m|) |m| := by
  suffices |A.1 i j| ≤ |m| from Finset.mem_Icc.mpr <| abs_le.mp this
  obtain ⟨h10, h00, h01, h11⟩ := h
  have h1 : 0 < |A.1 1 1| := (abs_nonneg _).trans_lt h11
  have h2 : 0 < |A.1 0 0| := abs_pos.mpr h00.ne'
  fin_cases i <;> fin_cases j
  · simpa only [← abs_mul, A_c_eq_zero h10] using (le_mul_iff_one_le_right h2).mpr h1
  · simpa only [← abs_mul, A_c_eq_zero h10] using h11.le.trans (le_mul_of_one_le_left h1.le h2)
  · simp_all
  · simpa only [← abs_mul, A_c_eq_zero h10] using (le_mul_iff_one_le_left h1).mpr h2

