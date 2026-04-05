import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_injective : Function.Injective (ofUnits (M := M)) :=
  ofUnits_units_gci.l_injective

