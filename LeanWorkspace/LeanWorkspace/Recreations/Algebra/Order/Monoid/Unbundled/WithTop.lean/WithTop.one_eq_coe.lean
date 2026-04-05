import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem one_eq_coe : 1 = (a : WithTop α) ↔ a = 1 := eq_comm.trans WithTop.coe_eq_one

