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


set_option backward.isDefEq.respectTransparency false in
theorem S_smul_four (A : Δ m) : S • S • S • S • A = A := by
  simp only [FixedDetMatrices.smul_def, ← mul_assoc, S_mul_S_eq, neg_mul, one_mul, mul_neg, neg_neg, Subtype.coe_eta]

