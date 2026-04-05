import Mathlib

variable {α β : Type*}

theorem pow_toDual [Pow α β] (a : α) (b : β) : a ^ toDual b = a ^ b := rfl

