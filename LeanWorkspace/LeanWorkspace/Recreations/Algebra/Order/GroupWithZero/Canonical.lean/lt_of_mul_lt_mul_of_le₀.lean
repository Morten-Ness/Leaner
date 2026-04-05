import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

theorem lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c ≤ a) : b < d := by
  have ha : a ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hh)
  rw [← inv_le_inv₀ (zero_lt_iff.2 ha) hc] at hh
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ hc.ne']
    using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hh h zero_le' (inv_pos.2 hc)

