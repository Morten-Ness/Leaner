import Mathlib

variable {R : Type u}

theorem up_intCast [IntCast R] (n : ℤ) : up (n : R) = n := rfl

