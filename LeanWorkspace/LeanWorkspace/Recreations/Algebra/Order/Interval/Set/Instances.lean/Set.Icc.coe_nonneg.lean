import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

omit [IsOrderedRing R] in
theorem coe_nonneg (x : Set.Icc (0 : R) 1) : 0 ≤ (x : R) := x.2.1

