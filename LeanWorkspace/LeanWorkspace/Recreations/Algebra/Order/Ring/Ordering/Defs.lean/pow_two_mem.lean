import Mathlib

variable (R : Type*) [CommRing R]

theorem pow_two_mem (P : RingPreordering R) (x : R) : x ^ 2 ∈ P := by aesop

