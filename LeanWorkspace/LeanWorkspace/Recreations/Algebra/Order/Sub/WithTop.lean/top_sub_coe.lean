import Mathlib

variable {α β : Type*}

variable [Sub α] [Bot α]

theorem top_sub_coe {a : α} : (⊤ : WithTop α) - a = ⊤ := rfl

