import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem untopD_one (d : α) : (1 : WithTop α).untopD d = 1 := rfl

