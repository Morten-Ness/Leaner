import Mathlib

variable {M R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem val_mul (x y : { x : R // 0 < x }) : ↑(x * y) = (x * y : R) := rfl

