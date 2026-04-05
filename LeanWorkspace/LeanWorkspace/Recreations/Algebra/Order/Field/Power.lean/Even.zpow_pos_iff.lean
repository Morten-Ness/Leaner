import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem Even.zpow_pos_iff (hn : Even n) (h : n ≠ 0) : 0 < a ^ n ↔ a ≠ 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add' (by simp [em']), mul_self_pos, zpow_ne_zero_iff (by simpa using h)]

