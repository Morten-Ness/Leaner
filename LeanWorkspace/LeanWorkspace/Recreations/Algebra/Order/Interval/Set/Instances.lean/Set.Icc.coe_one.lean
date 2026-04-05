import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem coe_one : ↑(1 : Set.Icc (0 : R) 1) = (1 : R) := rfl

