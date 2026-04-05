import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem fwdDiff_iter_comp_add (f : M → G) (m : M) (n : ℕ) (y : M) :
    Δ_[h]^[n] (fun r ↦ f (r + m)) y = (Δ_[h]^[n] f) (y + m) := by
  simp [fwdDiff_iter_eq_sum_shift, add_right_comm]

