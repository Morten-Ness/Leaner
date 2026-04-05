import Mathlib

variable {R : Type*}

theorem toDual_natCast [NatCast R] (n : ℕ) : toDual (n : R) = n := rfl

