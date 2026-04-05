import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem trop_sup_def (x y : Tropical R) : x ⊔ y = Tropical.trop (Tropical.untrop x ⊔ Tropical.untrop y) := rfl

