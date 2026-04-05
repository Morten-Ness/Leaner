import Mathlib

variable {M : Type*} [CommMonoid M]

theorem square_toSubsemigroup : (Submonoid.square M).toSubsemigroup = .square M := rfl

