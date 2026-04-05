import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem coe_eq_zero [Nontrivial R] {x : Set.Ico (0 : R) 1} : (x : R) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

