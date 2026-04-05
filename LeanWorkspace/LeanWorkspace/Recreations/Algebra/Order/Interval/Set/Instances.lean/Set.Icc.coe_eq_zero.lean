import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem coe_eq_zero {x : Set.Icc (0 : R) 1} : (x : R) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

