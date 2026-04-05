import Mathlib

variable {α β : Type*}

theorem toColex_mul [Mul α] (a b : α) : toColex (a * b) = toColex a * toColex b := rfl

