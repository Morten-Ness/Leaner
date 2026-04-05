import Mathlib

variable {α β : Type*}

theorem toLex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b := rfl

