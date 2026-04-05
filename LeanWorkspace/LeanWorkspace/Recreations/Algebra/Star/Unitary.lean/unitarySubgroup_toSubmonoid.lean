import Mathlib

variable {R : Type*}

variable {G : Type*} [Group G] [StarMul G]

theorem unitarySubgroup_toSubmonoid : (unitarySubgroup G).toSubmonoid = unitary G := rfl

