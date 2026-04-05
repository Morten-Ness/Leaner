import Mathlib

variable {α β : Type*}

theorem toDual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b := rfl

