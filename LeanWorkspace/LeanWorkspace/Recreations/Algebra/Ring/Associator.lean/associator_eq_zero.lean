import Mathlib

variable {R : Type*}

variable [NonUnitalRing R]

theorem associator_eq_zero : associator (R := R) = 0 :=
  associator_eq_zero_iff_associative.mpr inferInstance

