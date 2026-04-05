import Mathlib

variable {α β : Type*}

theorem toDual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b := rfl

