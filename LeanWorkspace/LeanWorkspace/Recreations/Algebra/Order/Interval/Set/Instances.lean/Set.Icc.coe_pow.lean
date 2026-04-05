import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem coe_pow (x : Set.Icc (0 : R) 1) (n : ℕ) : ↑(x ^ n) = ((x : R) ^ n) := rfl

