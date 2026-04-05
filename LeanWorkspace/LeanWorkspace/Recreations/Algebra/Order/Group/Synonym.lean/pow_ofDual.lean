import Mathlib

variable {α β : Type*}

theorem pow_ofDual [Pow α β] (a : α) (b : βᵒᵈ) : a ^ ofDual b = a ^ b := rfl

