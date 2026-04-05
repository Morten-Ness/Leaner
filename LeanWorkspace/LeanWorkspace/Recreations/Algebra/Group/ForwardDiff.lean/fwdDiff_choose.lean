import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem fwdDiff_choose (j : ℕ) : Δ_[1] (fun x ↦ x.choose (j + 1) : ℕ → ℤ) = fun x ↦ x.choose j := by
  ext n
  simp only [fwdDiff, choose_succ_succ' n j, cast_add, add_sub_cancel_right]

