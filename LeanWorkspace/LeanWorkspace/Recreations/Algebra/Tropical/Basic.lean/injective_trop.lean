import Mathlib

variable (R : Type u)

theorem injective_trop : Function.Injective (Tropical.trop : R → Tropical R) := Tropical.tropEquiv.injective

