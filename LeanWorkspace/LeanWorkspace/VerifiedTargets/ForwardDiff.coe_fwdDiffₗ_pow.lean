import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem coe_fwdDiffₗ_pow (n : ℕ) : ↑(fwdDiff_aux.fwdDiffₗ M G h ^ n) = (fwdDiff h)^[n] := by
  ext; rw [Module.End.pow_apply, fwdDiff_aux.coe_fwdDiffₗ]

