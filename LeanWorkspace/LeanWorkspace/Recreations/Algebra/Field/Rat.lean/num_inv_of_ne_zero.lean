import Mathlib

theorem num_inv_of_ne_zero {q : ℚ≥0} (hq : q ≠ 0) : q⁻¹.num = q.den := by
  rw [NNRat.inv_def, divNat, num, coe_mk, Rat.divInt_ofNat, ← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq),
    Int.natAbs_natCast]
  simpa using q.coprime_num_den.symm

