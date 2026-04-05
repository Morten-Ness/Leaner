import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_strictMono : StrictMono (ofUnits (M := M)) := ofUnits_units_gci.strictMono_l

