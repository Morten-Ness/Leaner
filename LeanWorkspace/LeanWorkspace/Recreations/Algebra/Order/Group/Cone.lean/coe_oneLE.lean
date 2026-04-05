import Mathlib

variable {H : Type*} [CommGroup H] [PartialOrder H] [IsOrderedMonoid H] {a : H}

theorem coe_oneLE : GroupCone.oneLE H = {x : H | 1 ≤ x} := rfl

