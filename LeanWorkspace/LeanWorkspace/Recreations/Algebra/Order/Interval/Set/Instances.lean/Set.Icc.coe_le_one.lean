import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

omit [IsOrderedRing R] in
theorem coe_le_one (x : Set.Icc (0 : R) 1) : (x : R) ≤ 1 := x.2.2

