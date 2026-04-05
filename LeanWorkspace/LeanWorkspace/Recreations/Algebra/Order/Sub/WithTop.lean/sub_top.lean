import Mathlib

variable {α β : Type*}

variable [Sub α] [Bot α]

theorem sub_top {a : WithTop α} : a - ⊤ = (⊥ : α) := by cases a <;> rfl

