import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem coe_ne_one {x : Set.Ioc (0 : R) 1} : (x : R) ≠ 1 ↔ x ≠ 1 := not_iff_not.mpr Set.Ioc.coe_eq_one

