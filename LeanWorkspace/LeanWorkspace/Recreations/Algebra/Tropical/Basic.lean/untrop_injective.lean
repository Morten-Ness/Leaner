import Mathlib

variable (R : Type u)

theorem untrop_injective : Function.Injective (Tropical.untrop : Tropical R → R) := fun _ _ => id

