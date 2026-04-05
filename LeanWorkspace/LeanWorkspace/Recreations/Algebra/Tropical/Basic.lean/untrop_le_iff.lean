import Mathlib

variable (R : Type u)

theorem untrop_le_iff [LE R] {x y : Tropical R} : Tropical.untrop x ≤ Tropical.untrop y ↔ x ≤ y := Iff.rfl

