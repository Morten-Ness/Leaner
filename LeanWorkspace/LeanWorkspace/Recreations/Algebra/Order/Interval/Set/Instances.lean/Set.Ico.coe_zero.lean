import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem coe_zero [Nontrivial R] : ↑(0 : Set.Ico (0 : R) 1) = (0 : R) := rfl

