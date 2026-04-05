import Mathlib

variable {𝕜 R M : Type*}

variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [LinearOrder M]
  [IsOrderedAddMonoid M] [Module R M] [PosSMulMono R M]

theorem abs_smul (a : R) (b : M) : |a • b| = |a| • |b| := by
  obtain ha | ha := le_total a 0 <;> obtain hb | hb := le_total b 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos,
      smul_nonpos_of_nonpos_of_nonneg, smul_nonneg_of_nonpos_of_nonpos]

