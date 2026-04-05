import Mathlib

variable {R : Type*}

theorem op_intCast [IntCast R] (n : ℤ) : op (n : R) = n := rfl

