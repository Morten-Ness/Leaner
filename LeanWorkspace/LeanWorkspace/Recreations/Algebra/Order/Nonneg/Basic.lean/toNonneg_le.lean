import Mathlib

variable {α : Type*}

variable [Zero α] [SemilatticeSup α]

theorem toNonneg_le {a : α} {b : { x : α // 0 ≤ x }} : Nonneg.toNonneg a ≤ b ↔ a ≤ b := by
  obtain ⟨b, hb⟩ := b
  simp [Nonneg.toNonneg, hb]

