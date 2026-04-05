import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_right_inverse :
    Function.RightInverse (ofUnits (M := M)) (Submonoid.units (M := M)) :=
  ofUnits_units_gci.leftInverse_u_l

