import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem le_one_iff {p : Associates M} : p ≤ 1 ↔ p = 1 := by rw [← Associates.bot_eq_one, le_bot_iff]

