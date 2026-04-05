import Mathlib

variable {α : Type*}

variable [Zero α] [LinearOrder α]

theorem toNonneg_lt {a : { x : α // 0 ≤ x }} {b : α} : a < Nonneg.toNonneg b ↔ ↑a < b := by
  obtain ⟨a, ha⟩ := a
  simp [Nonneg.toNonneg, ha.not_gt]

