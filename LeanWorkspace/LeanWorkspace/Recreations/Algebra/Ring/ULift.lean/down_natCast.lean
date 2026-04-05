import Mathlib

variable {R : Type u}

theorem down_natCast [NatCast R] (n : ℕ) : down (n : ULift R) = n := rfl

