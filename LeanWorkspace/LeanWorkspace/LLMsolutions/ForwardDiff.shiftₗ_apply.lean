import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem shiftₗ_apply (f : M → G) (y : M) : fwdDiff_aux.shiftₗ M G h f y = f (y + h) := by
  simp [fwdDiff_aux.shiftₗ, fwdDiff]
