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


theorem reduce_of_pos {A : Δ m} (hc : (A.1 1 0) = 0) (ha : 0 < A.1 0 0) :
    FixedDetMatrices.reduce A = (T ^ (-(A.1 0 1 / A.1 1 1))) • A := by
  rw [FixedDetMatrices.reduce]
  simp only [zpow_neg, Int.ediv_neg, neg_neg] at *
  simp_rw [if_pos hc, if_pos ha]

