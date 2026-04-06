FAIL
import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem coe_fwdDiffₗ_pow (n : ℕ) : ↑(fwdDiff_aux.fwdDiffₗ M G h ^ n) = (fwdDiff h)^[n] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [pow_succ, LinearMap.coe_mul, ih]
      rfl
