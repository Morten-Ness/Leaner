import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem coe_le_one [LE α] {a : α} : (a : WithTop α) ≤ 1 ↔ a ≤ 1 := coe_le_coe

