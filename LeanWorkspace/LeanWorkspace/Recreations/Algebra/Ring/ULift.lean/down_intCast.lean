import Mathlib

variable {R : Type u}

theorem down_intCast [IntCast R] (n : ℤ) : down (n : ULift R) = n := rfl

