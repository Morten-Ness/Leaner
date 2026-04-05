import Mathlib

variable {G : Type*} [CommGroup G]

theorem coe_square : Subgroup.square G = {s : G | IsSquare s} := rfl

