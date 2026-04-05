import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem coe_eq_one {x : Set.Icc (0 : R) 1} : (x : R) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

