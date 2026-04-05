import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] {a b : WithTop α}

theorem le_of_untop₀_le_untop₀ (ha : a ≠ ⊤) (h : a.untop₀ ≤ b.untop₀) : a ≤ b := by
  lift a to α using ha
  by_cases hb : b = ⊤
  · simp_all
  lift b to α using hb
  simp_all

