import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem coe_zero : ↑(0 : Set.Icc (0 : R) 1) = (0 : R) := rfl

