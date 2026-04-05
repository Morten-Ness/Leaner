import Mathlib

variable {α : Type u} {β : Type v}

theorem one_lt_top [One α] [LT α] : (1 : WithTop α) < ⊤ := coe_lt_top _

