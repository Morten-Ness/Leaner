import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem coe_lt_one [LT α] {a : α} : (a : WithTop α) < 1 ↔ a < 1 := coe_lt_coe

