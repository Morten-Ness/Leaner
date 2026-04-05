import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem shiftₗ_pow_apply (f : M → G) (k : ℕ) (y : M) : (fwdDiff_aux.shiftₗ M G h ^ k) f y = f (y + k • h) := by
  induction k generalizing f with
  | zero => simp
  | succ k IH => simp [pow_add, IH (fwdDiff_aux.shiftₗ M G h f), fwdDiff_aux.shiftₗ_apply, add_assoc, add_nsmul]

