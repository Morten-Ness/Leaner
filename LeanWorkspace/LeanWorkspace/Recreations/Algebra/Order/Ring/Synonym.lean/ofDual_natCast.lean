import Mathlib

variable {R : Type*}

theorem ofDual_natCast [NatCast R] (n : ℕ) : (ofDual n : R) = n := rfl

