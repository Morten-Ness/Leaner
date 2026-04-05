import Mathlib

variable {α β : Type*}

variable [Sub α] [Bot α]

theorem sub_ne_top_iff {a b : WithTop α} : a - b ≠ ⊤ ↔ a ≠ ⊤ ∨ b = ⊤ := by simp [or_iff_not_imp_left]

protected

