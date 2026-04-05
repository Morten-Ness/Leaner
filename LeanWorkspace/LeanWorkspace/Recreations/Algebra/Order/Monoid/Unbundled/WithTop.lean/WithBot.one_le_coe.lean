import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem one_le_coe [LE α] : 1 ≤ (a : WithBot α) ↔ 1 ≤ a := coe_le_coe

