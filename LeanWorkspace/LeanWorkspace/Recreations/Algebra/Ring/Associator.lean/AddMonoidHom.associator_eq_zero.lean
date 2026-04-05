import Mathlib

variable {R : Type*}

variable [NonUnitalRing R]

theorem associator_eq_zero : AddMonoidHom.associator (R := R) = 0 :=
  AddMonoidHom.associator_eq_zero_iff_associative.mpr inferInstance

