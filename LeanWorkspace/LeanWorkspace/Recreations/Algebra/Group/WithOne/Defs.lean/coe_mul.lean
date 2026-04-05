import Mathlib

variable {α : Type u}

theorem coe_mul [Mul α] (a b : α) : (↑(a * b) : WithOne α) = a * b := rfl

