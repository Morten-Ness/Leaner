import Mathlib

variable {H : Type*} [CommGroup H] [PartialOrder H] [IsOrderedMonoid H] {a : H}

theorem oneLE_toSubmonoid : (GroupCone.oneLE H).toSubmonoid = .oneLE H := rfl

