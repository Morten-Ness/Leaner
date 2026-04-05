import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R} (p n : ℕ)

variable [hR : ExpChar R p]

theorem sub_pow_expChar_pow_of_commute (h : Commute x y) :
    (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_pow_of_commute _ _ (h.sub_left rfl)]

