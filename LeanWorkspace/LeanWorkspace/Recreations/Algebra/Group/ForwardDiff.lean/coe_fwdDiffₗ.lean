import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem coe_fwdDiffₗ : ↑(fwdDiff_aux.fwdDiffₗ M G h) = fwdDiff h := rfl

