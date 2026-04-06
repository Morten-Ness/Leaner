FAIL
import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem shiftₗ_pow_apply (f : M → G) (k : ℕ) (y : M) : (fwdDiff_aux.shiftₗ M G h ^ k) f y = f (y + k • h) := by
  induction k generalizing y with
  | zero =>
      simp [fwdDiff_aux.shiftₗ]
  | succ k ih =>
      rw [pow_succ]
      change (fwdDiff_aux.shiftₗ M G h) ((fwdDiff_aux.shiftₗ M G h ^ k) f) y = f (y + (k + 1) • h)
      simp [fwdDiff_aux.shiftₗ, ih, succ_nsmul, add_assoc]
