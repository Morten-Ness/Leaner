import Mathlib

variable {M : Type*} [CommMonoid M]

theorem coe_square : Submonoid.square M = {s : M | IsSquare s} := rfl

