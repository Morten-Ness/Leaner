import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem shift_eq_sum_fwdDiff_iter (f : M → G) (n : ℕ) (y : M) :
    f (y + n • h) = ∑ k ∈ range (n + 1), n.choose k • Δ_[h]^[k] f y := by
  convert congr_fun (LinearMap.congr_fun
      ((Commute.one_right (fwdDiff_aux.fwdDiffₗ M G h)).add_pow n) f) y using 1
  · rw [← fwdDiff_aux.shiftₗ_pow_apply h f, fwdDiff_aux.shiftₗ]
  · simp [Module.End.pow_apply, fwdDiff_aux.coe_fwdDiffₗ]

