import Mathlib

variable {S : Type*} [CommSemigroup S]

theorem coe_square : Subsemigroup.square S = {s : S | IsSquare s} := rfl

