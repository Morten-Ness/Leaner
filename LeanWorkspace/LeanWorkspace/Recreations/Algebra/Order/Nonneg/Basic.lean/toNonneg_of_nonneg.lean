import Mathlib

variable {α : Type*}

variable [Zero α] [SemilatticeSup α]

theorem toNonneg_of_nonneg {a : α} (h : 0 ≤ a) : Nonneg.toNonneg a = ⟨a, h⟩ := by simp [Nonneg.toNonneg, h]

