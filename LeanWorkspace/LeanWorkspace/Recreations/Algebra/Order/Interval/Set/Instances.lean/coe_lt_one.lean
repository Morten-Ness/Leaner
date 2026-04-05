import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

omit [IsOrderedRing R] in
theorem coe_lt_one (x : Set.Ico (0 : R) 1) : (x : R) < 1 := x.2.2

