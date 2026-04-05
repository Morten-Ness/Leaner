import Mathlib

variable {α β : Type*}

variable [LE α] {x y : WithZero α} {a b : α}

theorem coe_le_iff : a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b := WithBot.coe_le_iff

