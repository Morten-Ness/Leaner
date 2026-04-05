import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits (M := M)) (Submonoid.units) :=
ofUnits_units_gci.gc

