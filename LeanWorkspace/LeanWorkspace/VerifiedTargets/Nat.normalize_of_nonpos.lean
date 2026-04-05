import Mathlib

theorem normalize_of_nonpos {z : ℤ} (h : z ≤ 0) : normalize z = -z := by
  obtain rfl | h := h.eq_or_lt
  · simp
  · rw [normalize_apply, Int.normUnit_eq, if_neg (not_le_of_gt h), Units.val_neg, Units.val_one,
      mul_neg_one]

