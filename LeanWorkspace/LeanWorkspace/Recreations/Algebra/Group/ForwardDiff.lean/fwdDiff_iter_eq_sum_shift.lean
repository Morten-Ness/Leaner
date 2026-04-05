import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem fwdDiff_iter_eq_sum_shift (f : M → G) (n : ℕ) (y : M) :
    Δ_[h]^[n] f y = ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • f (y + k • h) := by
  -- rewrite in terms of `(fwdDiff_aux.shiftₗ - 1) ^ n`
  have : fwdDiff_aux.fwdDiffₗ M G h = fwdDiff_aux.shiftₗ M G h - 1 := by simp only [fwdDiff_aux.shiftₗ, add_sub_cancel_right]
  rw [← fwdDiff_aux.coe_fwdDiffₗ, this, ← Module.End.pow_apply]
  -- use binomial theorem `Commute.add_pow` to expand this
  have : Commute (fwdDiff_aux.shiftₗ M G h) (-1) := (Commute.one_right _).neg_right
  convert congr_fun (LinearMap.congr_fun (this.add_pow n) f) y using 3
  · simp only [sub_eq_add_neg]
  · rw [LinearMap.sum_apply, sum_apply]
    congr 1 with k
    have : ((-1) ^ (n - k) * n.choose k : Module.End ℤ (M → G))
              = ↑((-1) ^ (n - k) * n.choose k : ℤ) := by norm_cast
    rw [mul_assoc, Module.End.mul_apply, this, Module.End.intCast_apply, map_smul,
      Pi.smul_apply, fwdDiff_aux.shiftₗ_pow_apply]

