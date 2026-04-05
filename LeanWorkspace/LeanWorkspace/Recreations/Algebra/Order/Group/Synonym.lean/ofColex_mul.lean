import Mathlib

variable {α β : Type*}

theorem ofColex_mul [Mul α] (a b : Colex α) : ofColex (a * b) = ofColex a * ofColex b := rfl

