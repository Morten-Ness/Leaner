import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem untrop_sup (x y : Tropical R) : Tropical.untrop (x ⊔ y) = Tropical.untrop x ⊔ Tropical.untrop y := rfl

