import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem coe_one : ↑(1 : Set.Ioc (0 : R) 1) = (1 : R) := rfl

