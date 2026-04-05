import Mathlib

variable {R : Type*}

theorem op_natCast [NatCast R] (n : ℕ) : op (n : R) = n := rfl

