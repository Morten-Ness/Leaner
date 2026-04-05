import Mathlib

open scoped Polynomial

theorem one_le_pow_mul_abs_eval_div {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {f : ℤ[X]} {a b : ℤ}
    (b0 : 0 < b) (fab : eval ((a : K) / b) (f.map (algebraMap ℤ K)) ≠ 0) :
    (1 : K) ≤ (b : K) ^ f.natDegree * |eval ((a : K) / b) (f.map (algebraMap ℤ K))| := by
  obtain ⟨ev, bi, bu, hF⟩ :=
    denomsClearable_natDegree (b := b) (algebraMap ℤ K) f a
      (by
        rw [eq_intCast, one_div_mul_cancel]
        rw [Int.cast_ne_zero]
        exact b0.ne.symm)
  obtain Fa := congr_arg abs hF
  rw [eq_one_div_of_mul_eq_one_left bu, eq_intCast, eq_intCast, abs_mul] at Fa
  rw [abs_of_pos (pow_pos (Int.cast_pos.mpr b0) _ : 0 < (b : K) ^ _), one_div, eq_intCast] at Fa
  rw [div_eq_mul_inv, ← Fa, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  refine Int.le_of_lt_add_one ((lt_add_iff_pos_left 1).mpr (abs_pos.mpr fun F0 => fab ?_))
  rw [eq_one_div_of_mul_eq_one_left bu, F0, one_div, eq_intCast, Int.cast_zero, zero_eq_mul] at hF
  rcases hF with hF | hF
  · exact (not_le.mpr b0 (le_of_eq (Int.cast_eq_zero.mp (eq_zero_of_pow_eq_zero hF)))).elim
  · rwa [div_eq_mul_inv]

