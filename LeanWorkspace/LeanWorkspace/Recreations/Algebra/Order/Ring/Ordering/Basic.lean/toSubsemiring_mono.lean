import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem toSubsemiring_mono : Monotone (toSubsemiring : RingPreordering R → _) := fun _ _ => id

