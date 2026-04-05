import Mathlib

variable {R : Type u}

theorem up_natCast [NatCast R] (n : ℕ) : up (n : R) = n := rfl

