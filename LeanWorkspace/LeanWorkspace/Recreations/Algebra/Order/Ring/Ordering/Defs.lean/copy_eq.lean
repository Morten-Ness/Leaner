import Mathlib

variable (R : Type*) [CommRing R]

variable (P : RingPreordering R) (S : Set R) (hS : S = P)

theorem copy_eq : P.copy S hS = S := rfl

