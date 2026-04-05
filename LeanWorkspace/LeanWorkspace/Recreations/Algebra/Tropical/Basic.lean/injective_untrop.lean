import Mathlib

variable (R : Type u)

theorem injective_untrop : Function.Injective (Tropical.untrop : Tropical R → R) := Tropical.tropEquiv.symm.injective

