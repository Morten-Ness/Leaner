import Mathlib

variable {α : Type*}

variable [Zero α] [SemilatticeSup α]

theorem coe_toNonneg {a : α} : (Nonneg.toNonneg a : α) = max a 0 := rfl

