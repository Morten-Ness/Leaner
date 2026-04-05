import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem coe_eq_one : (a : WithTop α) = 1 ↔ a = 1 := coe_eq_coe

