import Mathlib

variable {G : Type*} [CommGroup G]

theorem square_toSubmonoid : (Subgroup.square G).toSubmonoid = .square G := rfl

