import Mathlib

variable {M R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem val_pow (x : { x : R // 0 < x }) (n : ℕ) :
    ↑(x ^ n) = (x : R) ^ n := rfl

