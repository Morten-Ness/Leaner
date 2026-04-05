import Mathlib

variable {M : Type*} [Monoid M]

theorem units_left_inverse :
    Function.LeftInverse (units (M := M)) (Subgroup.ofUnits (M := M)) :=
  ofUnits_units_gci.leftInverse_u_l

