import Mathlib

variable (R : Type*) [CommRing R]

theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : RingPreordering R → _) := fun A B h => by ext; rw [h]

