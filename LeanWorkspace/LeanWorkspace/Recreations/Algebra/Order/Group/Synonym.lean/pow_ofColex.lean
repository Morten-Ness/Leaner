import Mathlib

variable {α β : Type*}

theorem pow_ofColex [Pow α β] (a : α) (b : Colex β) : a ^ ofColex b = a ^ b := rfl

