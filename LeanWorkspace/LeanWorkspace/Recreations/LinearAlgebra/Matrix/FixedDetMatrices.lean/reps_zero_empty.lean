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


theorem reps_zero_empty : FixedDetMatrices.reps 0 = ∅ := by
  rw [FixedDetMatrices.reps, Set.eq_empty_iff_forall_notMem]
  rintro A ⟨h₁, h₂, -, h₄⟩
  suffices |A.1 0 1| < 0 by linarith [abs_nonneg (A.1 0 1)]
  have := A_c_eq_zero h₁
  simp_all [h₂.ne']

noncomputable instance repsFintype (k : ℤ) : Fintype (FixedDetMatrices.reps k) := by
  let H := Finset.Icc (-|k|) |k|
  let H4 := Fin 2 → Fin 2 → H
  apply Fintype.ofInjective (β := H4) (f := fun M i j ↦ ⟨M.1.1 i j, FixedDetMatrices.reps_entries_le_m' M.2 i j⟩)
  intro M N h
  ext i j
  simpa only [Subtype.mk.injEq] using congrFun₂ h i j

