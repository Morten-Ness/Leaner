import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
theorem coe_le_one (x : Set.Ioc (0 : R) 1) : (x : R) ≤ 1 := x.2.2

