import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem coe_mul (x y : Set.Ico (0 : R) 1) : ↑(x * y) = (x * y : R) := rfl

