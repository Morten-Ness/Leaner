import Mathlib

variable {M : Type*} [Monoid M]

theorem units_surjective : Function.Surjective (units (M := M)) :=
  ofUnits_units_gci.u_surjective

