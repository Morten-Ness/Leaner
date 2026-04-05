import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] {a b : WithTop α}

theorem untop₀_le_untop₀_iff (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a.untop₀ ≤ b.untop₀ ↔ a ≤ b := by
  lift a to α using ha
  lift b to α using hb
  simp

