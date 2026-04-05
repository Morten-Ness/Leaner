import Mathlib

variable (R : Type*) [CommRing R]

theorem mem_of_isSquare (P : RingPreordering R) {x : R} (hx : IsSquare x) : x ∈ P := RingPreordering.mem_of_isSquare' _ hx

