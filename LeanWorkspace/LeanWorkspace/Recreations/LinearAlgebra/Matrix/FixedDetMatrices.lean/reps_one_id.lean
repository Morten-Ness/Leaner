import Mathlib

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

variable {m : ℤ}

variable {C : Δ m → Prop}

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


private theorem prop_red_S (hS : ∀ B, C B → C (S • B)) (B) : C (S • B) ↔ C B := by
  refine ⟨?_, hS _⟩
  intro ih
  rw [← (FixedDetMatrices.S_smul_four B)]
  solve_by_elim


private theorem prop_red_T (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C (T • B)) (B) :
    C (T • B) ↔ C B := by
  refine ⟨?_, hT _⟩
  intro ih
  rw [show B = T⁻¹ • T • B by simp, ← FixedDetMatrices.T_S_rel_smul]
  solve_by_elim (maxDepth := 10)


private theorem prop_red_T_pow (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C (T • B)) :
     ∀ B (n : ℤ), C (T ^ n • B) ↔ C B := by
  intro B n
  induction n with
  | zero => simp only [zpow_zero, one_smul]
  | succ n hn =>
    simpa only [add_comm (n : ℤ), zpow_add _ 1, ← smul_eq_mul, zpow_one, smul_assoc,
      prop_red_T hS hT]
  | pred m hm =>
    rwa [sub_eq_neg_add, zpow_add, zpow_neg_one, ← prop_red_T hS hT, mul_smul, smul_inv_smul]


theorem reps_one_id (A : FixedDetMatrix (Fin 2) ℤ 1) (a1 : A.1 1 0 = 0) (a4 : 0 < A.1 0 0)
    (a6 : |A.1 0 1| < |(A.1 1 1)|) : A = (1 : SL(2, ℤ)) := by
  have := Int.mul_eq_one_iff_eq_one_or_neg_one.mp (A_c_eq_zero a1)
  ext i j
  fin_cases i <;> fin_cases j <;> aesop

