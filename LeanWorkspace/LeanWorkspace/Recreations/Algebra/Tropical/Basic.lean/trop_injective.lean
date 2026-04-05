import Mathlib

variable (R : Type u)

theorem trop_injective : Function.Injective (Tropical.trop : R → Tropical R) := fun _ _ => id

