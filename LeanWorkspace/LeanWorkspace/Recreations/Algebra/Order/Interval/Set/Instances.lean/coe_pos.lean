import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
theorem coe_pos (x : Set.Ioc (0 : R) 1) : 0 < (x : R) := x.2.1

