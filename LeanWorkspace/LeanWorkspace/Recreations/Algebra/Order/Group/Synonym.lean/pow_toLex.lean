import Mathlib

variable {α β : Type*}

theorem pow_toLex [Pow α β] (a : α) (b : β) : a ^ toLex b = a ^ b := rfl

