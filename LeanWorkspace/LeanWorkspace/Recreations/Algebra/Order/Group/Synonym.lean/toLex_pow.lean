import Mathlib

variable {α β : Type*}

theorem toLex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b := rfl

