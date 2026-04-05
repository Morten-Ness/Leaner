import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : RingPreordering R → _) := fun _ _ => id

