import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem coe_pow (x : Set.Ioc (0 : R) 1) (n : ℕ) : ↑(x ^ n) = ((x : R) ^ n) := rfl

