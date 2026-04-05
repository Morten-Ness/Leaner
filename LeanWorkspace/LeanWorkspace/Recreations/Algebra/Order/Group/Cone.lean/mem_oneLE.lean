import Mathlib

variable {H : Type*} [CommGroup H] [PartialOrder H] [IsOrderedMonoid H] {a : H}

theorem mem_oneLE : a ∈ GroupCone.oneLE H ↔ 1 ≤ a := Iff.rfl

