import Mathlib

variable {α β : Type*}

theorem ofColex_pow [Pow α β] (a : Colex α) (b : β) : ofColex (a ^ b) = ofColex a ^ b := rfl

