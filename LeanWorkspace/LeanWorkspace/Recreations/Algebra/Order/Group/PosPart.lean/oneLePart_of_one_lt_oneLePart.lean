import Mathlib

variable {α : Type*}

variable [LinearOrder α] [Group α] {a b : α}

theorem oneLePart_of_one_lt_oneLePart (ha : 1 < a⁺ᵐ) : a⁺ᵐ = a := by
  rw [oneLePart_def, right_lt_sup, not_le] at ha; exact oneLePart_eq_self.2 ha.le

