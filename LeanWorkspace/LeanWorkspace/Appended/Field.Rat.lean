import Mathlib

section

theorem den_inv_of_ne_zero {q : ℚ≥0} (hq : q ≠ 0) : q⁻¹.den = q.num := by
  rw [NNRat.inv_def, divNat, den, coe_mk, Rat.divInt_ofNat, ← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]
  simpa using q.coprime_num_den.symm

end

section

theorem div_def (p q : ℚ≥0) : p / q = divNat (p.num * q.den) (p.den * q.num) := by
  ext; simp [Rat.div_def', num_coe, den_coe]

end

section

theorem inv_def (q : ℚ≥0) : q⁻¹ = divNat q.den q.num := by ext; simp [Rat.inv_def, num_coe, den_coe]

end

section

theorem num_div_den (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q := by
  ext1
  rw [coe_div, coe_natCast, coe_natCast, num, ← Int.cast_natCast]
  exact (cast_def _).symm

end

section

theorem num_inv_of_ne_zero {q : ℚ≥0} (hq : q ≠ 0) : q⁻¹.num = q.den := by
  rw [NNRat.inv_def, divNat, num, coe_mk, Rat.divInt_ofNat, ← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq),
    Int.natAbs_natCast]
  simpa using q.coprime_num_den.symm

end
