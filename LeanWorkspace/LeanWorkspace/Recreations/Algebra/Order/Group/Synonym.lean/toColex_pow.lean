import Mathlib

variable {α β : Type*}

theorem toColex_pow [Pow α β] (a : α) (b : β) : toColex (a ^ b) = toColex a ^ b := rfl

