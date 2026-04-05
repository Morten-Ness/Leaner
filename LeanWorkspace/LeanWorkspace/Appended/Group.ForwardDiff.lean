import Mathlib

section

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem coe_fwdDiffₗ_pow (n : ℕ) : ↑(fwdDiff_aux.fwdDiffₗ M G h ^ n) = (fwdDiff h)^[n] := by
  ext; rw [Module.End.pow_apply, fwdDiff_aux.coe_fwdDiffₗ]

end

section

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem shiftₗ_apply (f : M → G) (y : M) : fwdDiff_aux.shiftₗ M G h f y = f (y + h) := by simp [fwdDiff_aux.shiftₗ, fwdDiff]

end

section

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem shiftₗ_pow_apply (f : M → G) (k : ℕ) (y : M) : (fwdDiff_aux.shiftₗ M G h ^ k) f y = f (y + k • h) := by
  induction k generalizing f with
  | zero => simp
  | succ k IH => simp [pow_add, IH (fwdDiff_aux.shiftₗ M G h f), fwdDiff_aux.shiftₗ_apply, add_assoc, add_nsmul]

end
