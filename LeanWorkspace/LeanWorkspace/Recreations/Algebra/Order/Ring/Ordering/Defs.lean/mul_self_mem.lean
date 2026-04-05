import Mathlib

variable (R : Type*) [CommRing R]

theorem mul_self_mem (P : RingPreordering R) (x : R) : x * x ∈ P := by aesop

