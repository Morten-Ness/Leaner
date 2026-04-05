import Mathlib

variable {α β : Type*}

theorem pow_toColex [Pow α β] (a : α) (b : β) : a ^ toColex b = a ^ b := rfl

