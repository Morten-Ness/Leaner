import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem coe_mul (x y : Set.Ioo (0 : R) 1) : ↑(x * y) = (x * y : R) := rfl

