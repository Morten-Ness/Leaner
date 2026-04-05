import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem coe_ne_zero {x : Set.Icc (0 : R) 1} : (x : R) ≠ 0 ↔ x ≠ 0 := not_iff_not.mpr Set.Icc.coe_eq_zero

