import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R} (p n : ℕ)

variable [hR : ExpChar R p]

theorem sub_pow_expChar_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p := by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_of_commute _ (h.sub_left rfl)]

