import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem one_lt_coe [LT α] {a : α} : 1 < (a : WithTop α) ↔ 1 < a := coe_lt_coe

